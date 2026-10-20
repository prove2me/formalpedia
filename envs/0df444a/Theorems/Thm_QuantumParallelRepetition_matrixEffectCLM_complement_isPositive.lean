-- Prove2me | Theorems.Thm_QuantumParallelRepetition_matrixEffectCLM_complement_isPositive
-- name    : QuantumParallelRepetition.matrixEffectCLM_complement_isPositive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:43.235103+00:00
-- url     : https://prove2.me/theorems/7e308ef2-5e4c-4f3d-8825-a8661d203eb2
-- title:
--   QuantumParallelRepetition.matrixEffectCLM_complement_isPositive
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | QuantumParallelRepetition | external Lean 4.33.1 validation; bundle SHA256 d8765170d1380c2591d50d87f9ea8fe3c5625537d968525072fc32b227592634

import Mathlib
import Definitions.Def_QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem QuantumParallelRepetition.matrixEffectCLM_complement_isPositive
    {d : Type*} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : (1 - E).PosSemidef) :
    (1 - Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) E).IsPositive := by sorry
