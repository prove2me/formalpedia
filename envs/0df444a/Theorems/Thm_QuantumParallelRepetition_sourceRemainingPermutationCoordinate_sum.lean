-- Prove2me | Theorems.Thm_QuantumParallelRepetition_sourceRemainingPermutationCoordinate_sum
-- name    : QuantumParallelRepetition.sourceRemainingPermutationCoordinate_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/6b875231-4e14-43dd-94e0-511c6a2cce29
-- title:
--   QuantumParallelRepetition.sourceRemainingPermutationCoordinate_sum
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
open scoped BigOperators

theorem QuantumParallelRepetition.sourceRemainingPermutationCoordinate_sum
    {T : Type*} [AddCommMonoid T]
    {n : ℕ} (D : Finset (Fin n))
    (π : SourceRemainingPermutation D)
    (f : Fin n → T) :
    (∑ k : Fin (Finset.univ \ D).card,
      f (sourceRemainingPermutationCoordinate D π k)) =
      ∑ i : SourceRemainingCoordinate D, f i.val := by sorry
