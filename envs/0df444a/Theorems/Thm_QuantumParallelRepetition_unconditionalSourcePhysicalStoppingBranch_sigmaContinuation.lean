-- Prove2me | Theorems.Thm_QuantumParallelRepetition_unconditionalSourcePhysicalStoppingBranch_sigmaContinuation
-- name    : QuantumParallelRepetition.unconditionalSourcePhysicalStoppingBranch_sigmaContinuation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:47.127294+00:00
-- url     : https://prove2.me/theorems/4f61b6ab-9852-411a-8051-a03d4d1f0bf0
-- title:
--   QuantumParallelRepetition.unconditionalSourcePhysicalStoppingBranch_sigmaContinuation
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

theorem QuantumParallelRepetition.unconditionalSourcePhysicalStoppingBranch_sigmaContinuation
    {R κ : Type} [Fintype R] [DecidableEq R]
    [Fintype κ] [DecidableEq κ]
    (U V : R → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ ((Σ _ : R, κ) × (Σ _ : R, κ)))
    (r s : R) :
    actualStoppingBranchVector
      (dSVUniformDensityPhysicalAsyncSigmaContinuation U V z)
      r s =
      toLp 2
        ((((U r : Matrix κ κ ℂ) ⊗ₖ (V s : Matrix κ κ ℂ)).mulVec
          (ofLp (actualStoppingBranchVector z r s)))) := by sorry
