-- Prove2me | Theorems.Thm_QuantumParallelRepetition_purificationRangeProjection_complement_compression
-- name    : QuantumParallelRepetition.purificationRangeProjection_complement_compression
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.843984+00:00
-- url     : https://prove2.me/theorems/9654b1b5-37fe-40e9-871e-b04104065331
-- title:
--   QuantumParallelRepetition.purificationRangeProjection_complement_compression
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
set_option maxHeartbeats 400000

theorem QuantumParallelRepetition.purificationRangeProjection_complement_compression
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    Matrix.conjTranspose Γ *
        (1 - purificationRangeProjection F hF Γ) * Γ = 0 := by sorry
