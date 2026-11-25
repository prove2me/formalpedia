-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_contDiff_dualNorm_sq_2f90cd236ef9
-- name    : P2M_GroundTheory_Heights__Heights_HermNorm_contDiff_dualNorm_sq_2f90cd236ef9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:48.88734+00:00
-- url     : https://prove2.me/theorems/76cc857f-12c9-4c09-abeb-c0e14173e590
-- title:
--   P2 M Ground Theory Heights  Heights Herm Norm cont Diff dual Norm sq 2f90cd236ef9: P2 M Ground Theory Heights  Heights Herm Norm cont Diff dual Norm sq 2f90cd236ef9
-- statement:
--   The P2 M Ground Theory Heights  Heights Herm Norm cont Diff dual Norm sq 2f90cd236ef9 construction uses the P2 M Ground Theory Heights  Heights Herm Norm cont Diff dual Norm sq 2f90cd236ef9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StSliceCutOffLimit.lean#L40-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PFsLogSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutOffLimit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_HermNorm_contDiff_dualNorm_sq_2f90cd236ef9 (h : HermNorm n) :
    ContDiff ℝ ∞ fun y : Fin n → ℂ => h.dualNorm y ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermNorm».«contDiff_dualNorm_sq» := P2M_GroundTheory_Heights__Heights_HermNorm_contDiff_dualNorm_sq_2f90cd236ef9
