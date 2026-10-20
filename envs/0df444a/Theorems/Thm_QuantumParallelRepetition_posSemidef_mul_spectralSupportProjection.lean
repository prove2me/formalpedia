-- Prove2me | Theorems.Thm_QuantumParallelRepetition_posSemidef_mul_spectralSupportProjection
-- name    : QuantumParallelRepetition.posSemidef_mul_spectralSupportProjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/82e36cfe-5b4e-4eea-8440-62db99237747
-- title:
--   QuantumParallelRepetition.posSemidef_mul_spectralSupportProjection
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

theorem QuantumParallelRepetition.posSemidef_mul_spectralSupportProjection
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hF : F.PosSemidef) (hA : A.PosSemidef)
    (hsub : (F - A).PosSemidef) :
    A * spectralSupportProjection F hF = A := by sorry
