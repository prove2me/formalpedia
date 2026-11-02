-- Prove2me | Theorems.Thm_TensorAdjacencyLookup8_lookupProg_exec
-- name    : TensorAdjacencyLookup8.lookupProg_exec
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T22:03:26.408258+00:00
-- url     : https://prove2.me/theorems/d5886a7d-392c-4169-a765-a374b4d5645d
-- title:
--   Correctness of row-major stack lookup
-- statement:
--   Let $v$ be a natural number and let $i,j<v$. Given a length-$v^2$ list representing a matrix in row-major order, the fixed eight-stack program prepends the entry at offset $iv+j$ to an arbitrary output tail. It preserves the matrix and unary dimension and index stacks, clears all scratch stacks, and terminates within $50(v+1)^2$ structured-program steps.

import Definitions.Def_TensorAdjacencyLookup8
open CookPvsNP ProjSchedTW.Complexity

theorem TensorAdjacencyLookup8.lookupProg_exec (v i j : ℕ) (data tail : List BSym)
    (hi : i < v) (hj : j < v) (hlen : data.length = v*v) :
    ∃ steps, steps ≤ 50*(v+1)^2 ∧
      TensorAdjacencyLookup8.lookupProg.Exec
        (TensorAdjacencyLookup8.store data (List.replicate v .one)
          (List.replicate i .one) (List.replicate j .one) tail [] [] [])
        (TensorAdjacencyLookup8.store data (List.replicate v .one)
          (List.replicate i .one) (List.replicate j .one)
          (data.getD (i*v+j) .zero :: tail) [] [] []) steps := by
  sorry
