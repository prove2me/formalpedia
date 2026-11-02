-- Prove2me | Theorems.Thm_TensorUnaryHalf_halfProg_exec
-- name    : TensorUnaryHalf.halfProg_exec
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T21:32:59.340795+00:00
-- url     : https://prove2.me/theorems/df2275c8-e59e-4c17-acd1-9c1a4850e86a
-- title:
--   Correctness and exact running time of unary halving
-- statement:
--   For every natural number $n$, the fixed three-stack halving program consumes a unary counter of length $n$, prepends $\lfloor n/2\rfloor$ unary symbols to the quotient stack, and prepends one marker to the parity stack exactly when $n$ is odd. Both original stack tails are preserved, and execution takes exactly $6\lceil n/2\rceil+1$ steps. This is a building block for converting unary magnitudes to binary encodings.

import Definitions.Def_TensorUnaryHalf
open CookPvsNP ProjSchedTW.Complexity

theorem TensorUnaryHalf.halfProg_exec (n : ℕ) (quotientTail parityTail : List BSym) :
    TensorUnaryHalf.halfProg.Exec
      (TensorUnaryHalf.store (List.replicate n .one) quotientTail parityTail)
      (TensorUnaryHalf.store [] (List.replicate (n/2) .one ++ quotientTail)
        ((if n % 2 = 0 then [] else [.one]) ++ parityTail))
      (6*((n+1)/2)+1) := by
  sorry
