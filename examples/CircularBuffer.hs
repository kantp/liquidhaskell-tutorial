{-# LANGUAGE FlexibleContexts #-}
{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
module CircularBuffer
       ( -- * Datatype, allocation, and deallocation
         ByteBuffer
       , new, free, with
         -- * Feeding new input
       , copyByteString
         -- * Consuming bytes from the buffer
       , consume
         -- * Exceptions
       , ByteBufferException (..)
       )
       where


import           Control.Applicative
import           Control.Exception (SomeException, throwIO)
import           Control.Exception.Lifted (Exception, bracket, catch)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Control.Monad.Trans.Control (MonadBaseControl)
import           Data.ByteString (ByteString)
import qualified Data.ByteString.Internal as BS
import           Data.IORef
import           Data.Maybe (fromMaybe)
import           Data.Typeable (Typeable)
import           Data.Word
import           Foreign.ForeignPtr
import qualified Foreign.Marshal.Alloc as Alloc
import           Foreign.Marshal.Utils (copyBytes, moveBytes)
import           GHC.Ptr
import           Prelude
import qualified Foreign.C.Error as CE
import           Foreign.C.Types
import           System.Posix.Types (Fd (..))

{-@
data BBRef = BBRef
    { size :: {v: Int | ... }
    , start :: { v: Int | ... }
    , available :: { v: Int | ... }
    , ptr :: { v: Ptr Word8 | ... }
    }
@-}

data BBRef = BBRef
    { size :: {-# UNPACK #-} !Int
    , start :: {-# UNPACK #-} !Int
    , available :: {-# UNPACK #-} !Int
    , ptr :: {-# UNPACK #-} !(Ptr Word8)
    }

-- | Exception that is thrown when an invalid 'ByteBuffer' is being used that is no longer valid.
--
-- A 'ByteBuffer' is considered to be invalid if
--
-- - it has explicitly been freed
-- - an Exception has occured during an operation that modified it
data ByteBufferException = ByteBufferException
    { _bbeLocation :: !String
      -- ^ function name that caused the exception
    , _bbeException :: !String
      -- ^ printed representation of the exception
    }
    deriving (Typeable, Eq)
instance Show ByteBufferException where
    show (ByteBufferException loc e) = concat
        ["ByteBufferException: ByteBuffer was invalidated because of Exception thrown in "
        , loc , ": ", e]
instance Exception ByteBufferException

type ByteBuffer = IORef (Either ByteBufferException BBRef)

-- | On any Exception, this will invalidate the ByteBuffer and re-throw the Exception.
--
-- Invalidating the 'ByteBuffer' includes freeing the underlying pointer.
bbHandler :: MonadIO m
    => String
       -- ^ location information: function from which the exception was thrown
    -> ByteBuffer
       -- ^ this 'ByteBuffer' will be invalidated when an Exception occurs
    -> (BBRef -> IO a)
    -> m a
bbHandler loc bb f = liftIO $ useBBRef f bb `catch` \(e :: SomeException) -> do
    readIORef bb >>= \case
        Right bbref -> do
            Alloc.free (ptr bbref)
            writeIORef bb (Left $ ByteBufferException loc (show e))
        Left _ -> return ()
    throwIO e
{-# INLINE bbHandler #-}

-- | Try to use the 'BBRef' of a 'ByteBuffer', or throw a 'ByteBufferException' if it's invalid.
useBBRef :: (BBRef -> IO a) -> ByteBuffer -> IO a
useBBRef f bb = readIORef bb >>= either throwIO f
{-# INLINE useBBRef #-}


-- | Allocates a new ByteBuffer with a given buffer size filling from
-- the given FillBuffer.
--
-- Note that 'ByteBuffer's created with 'new' have to be deallocated
-- explicitly using 'free'.  For automatic deallocation, consider
-- using 'with' instead.
new :: MonadIO m
    => Maybe Int
    -- ^ Size of buffer to allocate.  If 'Nothing', use the default
    -- value of 4MB
    -> m ByteBuffer
    -- ^ The byte buffer.
new ml = liftIO $ do
    let l = max 0 (fromMaybe (4*1024*1024) ml)
    newPtr <- Alloc.mallocBytes l
    newIORef $ Right BBRef
        { ptr = newPtr
        , size = l
        , start = 0
        , available = 0
        }
{-# INLINE new #-}

-- | Free a byte buffer.
free :: MonadIO m => ByteBuffer -> m ()
free bb = liftIO $ readIORef bb >>= \case
    Right bbref -> do
        Alloc.free $ ptr bbref
        writeIORef bb $
            Left (ByteBufferException "free" "ByteBuffer has explicitly been freed and is no longer valid.")
    Left _ -> return () -- the ByteBuffer is either invalid or has already been freed.
{-# INLINE free #-}

-- | Perform some action with a bytebuffer, with automatic allocation
-- and deallocation.
with :: (MonadIO m, MonadBaseControl IO m)
     => Maybe Int
     -- ^ Initial length of the 'ByteBuffer'.  If 'Nothing', use the
     -- default value of 4MB.
     -> (ByteBuffer -> m a)
     -> m a
with l action =
  bracket
    (new l)
    free
    action
{-# INLINE with #-}



copyByteString :: MonadIO m => ByteBuffer -> ByteString -> m ()
copyByteString bb bs = bbHandler "copyByteString" bb go
  where
    go bbref0 = do
        let (bsFptr, bsOffset, bsSize) = BS.toForeignPtr bs
        bbref@BBRef{..} <- if size bbref0 < bsSize + available bbref0
                           then enlargeBBRef bbref0 (bsSize + available bbref0)
                           else return bbref0
        let offset = start + available `mod` size
        withForeignPtr bsFptr $ \bsPtr -> do
            if offset + bsSize <= size
            then copyBytes (ptr `plusPtr` offset)
                           (bsPtr `plusPtr` bsOffset)
                           bsSize
            else do
                 let size1 = size - offset
                     size2 = bsSize - size1
                 copyBytes (ptr `plusPtr` offset)
                           (bsPtr `plusPtr` bsOffset)
                           size1
                 copyBytes ptr
                           (bsPtr `plusPtr` (bsOffset + size1))
                           size2
            writeIORef bb $ Right bbref { available = available + bsSize }

{-# INLINE copyByteString #-}

-- | Make sure the buffer is at least @minSize@ bytes long.
--
-- In order to avoid having to enlarge the buffer too often, we
-- multiply its size by a factor of 1.5 until it is at least @minSize@
-- bytes long.
{-@ enlargeBBRef :: b:BBRef -> i:Nat -> IO {v:BBRef | ... } @-}
enlargeBBRef :: BBRef -> Int -> IO BBRef
enlargeBBRef bbref minSize = do
        let getNewSize s | s >= minSize = s
            getNewSize s = getNewSize $ (ceiling . (*(1.5 :: Double)) . fromIntegral) (max 1 s)
            newSize = getNewSize (size bbref)
        -- possible optimisation: since reallocation might copy the
        -- bytes anyway, we could discard the consumed bytes,
        -- basically 'reset'ting the buffer on the fly.
        ptr' <- Alloc.reallocBytes (ptr bbref) newSize
        return BBRef { size = newSize
                     , start = start bbref
                     , available = available bbref
                     , ptr = ptr'
                     }
{-# INLINE enlargeBBRef #-}


consume :: MonadIO m => ByteBuffer -> Int -> m (Either Int ByteString)
consume bb n = bbHandler "consume" bb go
  where
    go bbref@BBRef{..}
        | available < n = return $ Left (n - available)
        | start + available <= size = do
              writeIORef bb $ Right bbref { start = start + n
                                          , available = available - n
                                          }
              Right <$> createBS (ptr `plusPtr` start) n
        | otherwise = do
              let size1 = size - start
                  size2 = n - size1
              writeIORef bb $ Right bbref { start = size1
                                          , available = available - n
                                          }
              Right <$> createBS2 (size1, ptr `plusPtr` start) (size2, ptr)
{-# INLINE consume #-}

-- | Create a 'ByteString' from a single pointer
{-@ createBS :: p:(Ptr Word8) -> {v:Nat | v <= plen p} -> IO ByteString @-}
createBS :: Ptr Word8 -> Int -> IO ByteString
createBS ptr n = do
  fp  <- mallocForeignPtrBytes n
  withForeignPtr fp (\p -> copyBytes p ptr n)
  return (BS.PS fp 0 n)
{-# INLINE createBS #-}

-- | Create a 'ByteString' from two pointers
{-@ createBS2 :: ... @-}
createBS2 :: (Int, Ptr Word8) -> (Int, Ptr Word8) -> IO ByteString
createBS2 (n1, ptr1) (n2, ptr2) = do
  let n = n1 + n2
  fp  <- mallocForeignPtrBytes n
  withForeignPtr fp $ \p -> do
      copyBytes p ptr1 n1
      copyBytes (p `plusPtr` n1) ptr2 n2
  return $ BS.PS fp 0 n
{-# INLINE createBS2 #-}



-- below are liquid haskell qualifiers, and specifications for external functions.

{-@ qualif FPLenPLen(v:Ptr a, fp:ForeignPtr a): fplen fp = plen v @-}

{-@ Foreign.Marshal.Alloc.mallocBytes :: l:Nat -> IO (PtrN a l) @-}
{-@ Foreign.Marshal.Alloc.reallocBytes :: Ptr a -> l:Nat -> IO (PtrN a l) @-}
{-@ type ForeignPtrN a N = {v:ForeignPtr a | fplen v = N} @-}
{-@ assume mallocForeignPtrBytes :: n:Nat -> IO (ForeignPtrN a n) @-}

-- writing down the specification for ByteString is not as straightforward as it seems at first: the constructor
--
-- PS (ForeignPtr Word8) Int Int
--
-- has actually four arguments after unboxing (the ForeignPtr is an
-- Addr# and ForeignPtrContents), so restriciting the length of the
-- ForeignPtr directly in the specification of the datatype does not
-- work.  Instead, I chose to write a specification for toForeignPtr.
-- It seems that the liquidhaskell parser has problems with variables
-- declared in a tuple, so I have to define the following measures to
-- get at the ForeignPtr, offset, and length.
--
-- This is a bit awkward, maybe there is an easier way.

_get1 :: (a,b,c) -> a
_get1 (x,_,_) = x
{-@ measure _get1 @-}
_get2 :: (a,b,c) -> b
_get2 (_,x,_) = x
{-@ measure _get2 @-}
_get3 :: (a,b,c) -> c
_get3 (_,_,x) = x
{-@ measure _get3 @-}

{-@ Data.ByteString.Internal.toForeignPtr :: ByteString -> {v:(ForeignPtr Word8, Int, Int) | (_get2 v >= 0) && (_get2 v <= (fplen (_get1 v))) && (_get3 v >= 0) && ((_get3 v) + (_get2 v)) <= (fplen (_get1 v))} @-}
