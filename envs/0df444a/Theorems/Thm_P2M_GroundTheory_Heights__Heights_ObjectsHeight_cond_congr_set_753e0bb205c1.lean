-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_congr_set_753e0bb205c1
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_congr_set_753e0bb205c1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:21:14.506789+00:00
-- url     : https://prove2.me/theorems/fbf60957-13cf-5145-9526-5d7061600652
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height cond congr set 753e0bb205c1: P2 M Ground Theory Heights  Heights Objects Height cond congr set 753e0bb205c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height cond congr set 753e0bb205c1 construction uses the P2 M Ground Theory Heights  Heights Objects Height cond congr set 753e0bb205c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L75-L77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_congr_set_753e0bb205c1 {α : Type*} [MeasurableSpace α] (μ : Measure α) {s t : Set α}
    (h : s =ᵐ[μ] t) : cond μ s = cond μ t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«cond_congr_set» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_congr_set_753e0bb205c1
