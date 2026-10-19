-- Prove2me | Theorems.Thm_QuantumParallelRepetition_spectralSupportProjection_mul_posSemidef
-- name    : QuantumParallelRepetition.spectralSupportProjection_mul_posSemidef
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/9cf456a4-dc57-4917-b067-d592b2b53dc4
-- title:
--   QuantumParallelRepetition.spectralSupportProjection_mul_posSemidef
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

theorem QuantumParallelRepetition.spectralSupportProjection_mul_posSemidef
    {d : Type*} [Fintype d] [DecidableEq d]
    {F A : Matrix d d ℂ}
    (hF : F.PosSemidef) (hA : A.PosSemidef)
    (hsub : (F - A).PosSemidef) :
    spectralSupportProjection F hF * A = A := by sorry
