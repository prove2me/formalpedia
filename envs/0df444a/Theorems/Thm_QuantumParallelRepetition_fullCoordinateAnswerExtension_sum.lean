-- Prove2me | Theorems.Thm_QuantumParallelRepetition_fullCoordinateAnswerExtension_sum
-- name    : QuantumParallelRepetition.fullCoordinateAnswerExtension_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/c4ac12fc-ab46-4d88-92ed-3f157fed37d9
-- title:
--   QuantumParallelRepetition.fullCoordinateAnswerExtension_sum
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

theorem QuantumParallelRepetition.fullCoordinateAnswerExtension_sum
    {T R : Type*} [Fintype T] [AddCommMonoid R]
    {n : ℕ} (D : Finset (Fin n)) (i : Fin n)
    (hiD : i ∉ D)
    (f : ({j : Fin n // j ∈ insert i D} → T) → R) :
    (∑ α : {j : Fin n // j ∈ insert i D} → T, f α) =
      ∑ α : {j : Fin n // j ∈ D} → T, ∑ a : T,
        f (fullCoordinateAnswerExtension D i α a) := by sorry
