-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateSelectedBranch_tensor_smul
-- name    : QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranch_tensor_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/8383fcda-9c97-49fb-b2af-3aadfcf1163d
-- title:
--   QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranch_tensor_smul
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
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranch_tensor_smul
    {s τ : Type*} [Fintype s] [Fintype τ]
    (c : ℝ) (stage : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ τ) :
    c • unconditionalMatchedVerifierTensor stage work =
      unconditionalMatchedVerifierTensor
        (c • stage) work := by sorry
