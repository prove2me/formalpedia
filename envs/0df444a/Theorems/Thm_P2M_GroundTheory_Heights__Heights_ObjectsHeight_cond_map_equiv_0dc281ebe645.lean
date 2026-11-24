-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_map_equiv_0dc281ebe645
-- name    : P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_map_equiv_0dc281ebe645
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:23.243021+00:00
-- url     : https://prove2.me/theorems/92ec1420-b73f-47be-8185-139d71ad98a3
-- title:
--   P2 M Ground Theory Heights  Heights Objects Height cond map equiv 0dc281ebe645: P2 M Ground Theory Heights  Heights Objects Height cond map equiv 0dc281ebe645
-- statement:
--   The P2 M Ground Theory Heights  Heights Objects Height cond map equiv 0dc281ebe645 construction uses the P2 M Ground Theory Heights  Heights Objects Height cond map equiv 0dc281ebe645 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/GaussNormEqCoeffGaussNorm.lean#L64-L67

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

theorem P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_map_equiv_0dc281ebe645 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (μ : Measure α) (s : Set β) : (cond μ (e ⁻¹' s)).map e = cond (μ.map e) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ObjectsHeight».«cond_map_equiv» := P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_map_equiv_0dc281ebe645
