-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartFormsRational_mem_of_mem_chartRing_7697125cad1f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartFormsRational_mem_of_mem_chartRing_7697125cad1f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:46:23.759523+00:00
-- url     : https://prove2.me/theorems/6b6b8b78-661e-521e-9f01-c19ccebc2b38
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Forms Rational mem of mem chart Ring 7697125cad1f: P2 M Ground Theory Heights  Heights Inter Chart Forms Rational mem of mem chart Ring 7697125cad1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Forms Rational mem of mem chart Ring 7697125cad1f construction uses the P2 M Ground Theory Heights  Heights Inter Chart Forms Rational mem of mem chart Ring 7697125cad1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartFormsRational.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartFormsRational.lean#L13-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsChartFormsRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDualRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDetRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartFormsRational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ChartDualRational
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartFormsRational_mem_of_mem_chartRing_7697125cad1f {Ω : Type*} [Field Ω] {ι : Type*} (x : ι → Ω) (i : ι) {a : Ω}
    (ha : a ∈ chartRing ℤ x i) : a ∈ chartFunField x i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartFormsRational».«mem_of_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Inter_ChartFormsRational_mem_of_mem_chartRing_7697125cad1f
