-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartAbsDens_nonneg_5c6d71b76cc7
-- name    : P2M_GroundTheory_Heights__Heights_chartAbsDens_nonneg_5c6d71b76cc7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:26.518498+00:00
-- url     : https://prove2.me/theorems/bb944e0b-0a8d-4557-be72-ee4ab38d8ca1
-- title:
--   P2 M Ground Theory Heights  Heights chart Abs Dens nonneg 5c6d71b76cc7: P2 M Ground Theory Heights  Heights chart Abs Dens nonneg 5c6d71b76cc7
-- statement:
--   The P2 M Ground Theory Heights  Heights chart Abs Dens nonneg 5c6d71b76cc7 construction uses the P2 M Ground Theory Heights  Heights chart Abs Dens nonneg 5c6d71b76cc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOff.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCutOff.lean#L35-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLogLogCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffGradient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOff
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
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_chartAbsDens_nonneg_5c6d71b76cc7 (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ chartAbsDens J A f φ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«chartAbsDens_nonneg» := P2M_GroundTheory_Heights__Heights_chartAbsDens_nonneg_5c6d71b76cc7
