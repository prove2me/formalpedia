-- Prove2me | Theorems.Thm_QuantumParallelRepetition_sourceHistoryFlag_sum
-- name    : QuantumParallelRepetition.sourceHistoryFlag_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/733a05e5-2ea0-4941-8ef9-dc0e813ba95f
-- title:
--   QuantumParallelRepetition.sourceHistoryFlag_sum
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem QuantumParallelRepetition.sourceHistoryFlag_sum
    {n : ℕ} (D : Finset (Fin n))
    (f : SourceHistoryFlag X Y A B D → ℝ) :
    (∑ r : SourceHistoryFlag X Y A B D, f r) =
      ∑ π : SourceRemainingPermutation D,
      ∑ k : Fin (Finset.univ \ D).card,
      ∑ r : FullCoordinateRevealHistory X Y n D
          (sourceRemainingPermutationPrefix D π k.castSucc)
          (sourceRemainingPermutationCoordinate D π k),
      ∑ α : {i : Fin n // i ∈ D} → A,
      ∑ β : {i : Fin n // i ∈ D} → B,
        f ⟨π, k, r, α, β⟩ := by sorry
