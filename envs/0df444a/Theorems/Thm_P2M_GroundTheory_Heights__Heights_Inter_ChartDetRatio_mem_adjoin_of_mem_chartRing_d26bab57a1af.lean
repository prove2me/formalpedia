-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_mem_adjoin_of_mem_chartRing_d26bab57a1af
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_mem_adjoin_of_mem_chartRing_d26bab57a1af
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:45:26.675903+00:00
-- url     : https://prove2.me/theorems/cd2621bb-0011-56a8-82eb-a83fabce180f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Chart Det Ratio mem adjoin of mem chart Ring d26bab57a1af: P2 M Ground Theory Heights  Heights Inter Chart Det Ratio mem adjoin of mem chart Ring d26bab57a1af
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Chart Det Ratio mem adjoin of mem chart Ring d26bab57a1af construction uses the P2 M Ground Theory Heights  Heights Inter Chart Det Ratio mem adjoin of mem chart Ring d26bab57a1af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDetRatio.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PChartDetRatio.lean#L11-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StChartDetRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PChartDetRatio
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_mem_adjoin_of_mem_chartRing_d26bab57a1af {Ω : Type} [Field Ω] [CharZero Ω] {ι : Type} (x : ι → Ω)
    (i₀ : ι) {a : Ω} (ha : a ∈ chartRing ℤ x i₀) :
    a ∈ IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ChartDetRatio».«mem_adjoin_of_mem_chartRing» := P2M_GroundTheory_Heights__Heights_Inter_ChartDetRatio_mem_adjoin_of_mem_chartRing_d26bab57a1af
