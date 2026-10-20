-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicLogPhasePureSource_apply
-- name    : QuantumParallelRepetition.dSVDensityRationalPublicLogPhasePureSource_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/276c16e7-aa80-4152-ab6a-8b9fc66d2cea
-- title:
--   QuantumParallelRepetition.dSVDensityRationalPublicLogPhasePureSource_apply
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

theorem QuantumParallelRepetition.dSVDensityRationalPublicLogPhasePureSource_apply
    (B N d L : ℕ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalPublicLogPhasePureSource
        B N d L ((φ, a), (ψ, b)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) := by sorry
