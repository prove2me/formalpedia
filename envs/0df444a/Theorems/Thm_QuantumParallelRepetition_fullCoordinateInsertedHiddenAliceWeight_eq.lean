-- Prove2me | Theorems.Thm_QuantumParallelRepetition_fullCoordinateInsertedHiddenAliceWeight_eq
-- name    : QuantumParallelRepetition.fullCoordinateInsertedHiddenAliceWeight_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/43d417ed-0391-40e4-aa5c-e1425bc0a353
-- title:
--   QuantumParallelRepetition.fullCoordinateInsertedHiddenAliceWeight_eq
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.fullCoordinateInsertedHiddenAliceWeight_eq
    (G : Game X Y A B) {n : ℕ}
    (D L : Finset (Fin n)) (i : Fin n)
    (r : FullCoordinateRevealHistory X Y n D L i)
    (x : X) (y : Y)
    (hidden : {j : Fin n //
      j ∈ fullHistoryRemaining n D (insert i L)} → X) :
    fullHistoryHiddenAliceWeight G
      (fullCoordinateInsertedHistory D L i r x y)
      ((fullCoordinateInsertedHiddenAliceEquiv (X := X) D L i).symm hidden) =
      fullHistoryHiddenAliceWeight G
        (fullCoordinateNewHistory D L i r x) hidden := by sorry
