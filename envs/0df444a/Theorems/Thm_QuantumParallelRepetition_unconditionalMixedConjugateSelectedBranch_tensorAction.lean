-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalMixedConjugateSelectedBranch_tensorAction
-- name    : QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranch_tensorAction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/87f5ec55-170d-41b7-9332-a1995b36e26a
-- title:
--   QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranch_tensorAction
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

theorem QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranch_tensorAction
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (U V : Matrix.unitaryGroup ι ℂ)
    (stage : EuclideanSpace ℂ (ι × ι))
    (work : EuclideanSpace ℂ τ) :
    unconditionalMixedConjugateSelectedBranchLocalAction
        U V
        (unconditionalMatchedVerifierTensor stage work) =
      unconditionalMatchedVerifierTensor
        (toLp 2
          ((((U : Matrix ι ι ℂ) ⊗ₖ
              (V : Matrix ι ι ℂ)).mulVec
            (ofLp stage)))) work := by sorry
