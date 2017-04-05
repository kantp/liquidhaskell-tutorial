This project contains two examples of using Liquid Haskell:

- `examples/ByteBuffer.hs` : This is the `ByteBuffer` used by the `store` library. It uses Liquid Haskell to prove that there are no out-of-bounds memory accesses.
- `examples/CircularBuffer.hs` : An circular buffer. It does not need to be reset, but wraps around at the end instead. It contains some Liquid Haskell annotations, and completing them is left as an execercise.

To do the exercises, you should first install Liquid Haskell https://github.com/ucsd-progsys/liquidhaskell, as described in https://github.com/ucsd-progsys/liquidhaskell/blob/develop/INSTALL.md.  This repository already has Liquid Haskell in its `stack.yaml` file, so you can just install `Z3` and then do

```
stack install liquidhaskell
```

After that, you can invoke LiquidHaskell via
```
stack exec -- liquid --prune-unsorted examples/ByteBuffer.hs
```
