-- Prove2me | Theorems.Thm_QuantumParallelRepetition_conditionedBobEffect_insert_eq_coordinate
-- name    : QuantumParallelRepetition.conditionedBobEffect_insert_eq_coordinate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/9f55eae4-42a1-44b7-823b-80a67c83e846
-- title:
--   QuantumParallelRepetition.conditionedBobEffect_insert_eq_coordinate
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
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.conditionedBobEffect_insert_eq_coordinate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : Fin n) (hiD : i ∉ D)
    (β : {j : Fin n // j ∈ D} → B)
    (b : B) (ys : Fin n → Y) :
    conditionedBobEffect G n S (insert i D)
      (fullCoordinateAnswerExtension D i β b) ys =
      conditionedBobCoordinateEffect G n S D β ys i b := by sorry
