-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_apply
-- name    : QuantumParallelRepetition.dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:44.608116+00:00
-- url     : https://prove2.me/theorems/a460705a-e0ab-40f3-b18c-65d9d3e1c100
-- title:
--   QuantumParallelRepetition.dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_apply
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

theorem QuantumParallelRepetition.dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_apply
    (B N d L m : ℕ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
        B N d L m
        (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
            B N d L m ((φ, a), i),
          dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
            B N d L m ((ψ, b), j)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) *
        embezzlementState m (i, j) := by sorry
