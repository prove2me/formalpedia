-- Prove2me | Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicLogPhasePhysicalAlignedLocalAction_apply
-- name    : QuantumParallelRepetition.dSVDensityRationalPublicLogPhasePhysicalAlignedLocalAction_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:45.425888+00:00
-- url     : https://prove2.me/theorems/01c18035-fd3f-4077-95be-da73208025ff
-- title:
--   QuantumParallelRepetition.dSVDensityRationalPublicLogPhasePhysicalAlignedLocalAction_apply
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
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

theorem QuantumParallelRepetition.dSVDensityRationalPublicLogPhasePhysicalAlignedLocalAction_apply
    (B N d L m : ℕ)
    (U V : Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    localUnitaryAction
      (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
        B N d L m
        (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
          B U))
      (dSVDensityRationalPublicLogPhaseActualTargetFirstLocalLift
        B N d L m
        (dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
          B V))
      (dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
        B N d L m)
      (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
          B N d L m ((φ, a), i),
       dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
          B N d L m ((ψ, b), j)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
      (∑ x : DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L,
        ∑ y : DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L,
          (U : Matrix
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) a x *
          (V : Matrix
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L)
            (DSVUniformDensityThresholdWholeHistoryLocalIndex
              N d L) ℂ) b y *
          dSVUniformDensityThresholdWholeHistorySharedState
            N d L (x, y)) *
      embezzlementState m (i, j) := by sorry
