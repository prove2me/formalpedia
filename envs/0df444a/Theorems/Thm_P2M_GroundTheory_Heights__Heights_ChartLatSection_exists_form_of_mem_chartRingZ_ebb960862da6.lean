-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_form_of_mem_chartRingZ_ebb960862da6
-- name    : P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_form_of_mem_chartRingZ_ebb960862da6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:15:35.650388+00:00
-- url     : https://prove2.me/theorems/212047a3-1df4-52f0-b062-01b270da36b5
-- title:
--   P2 M Ground Theory Heights  Heights Chart Lat Section exists form of mem chart Ring Z ebb960862da6: P2 M Ground Theory Heights  Heights Chart Lat Section exists form of mem chart Ring Z ebb960862da6
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Lat Section exists form of mem chart Ring Z ebb960862da6 construction uses the P2 M Ground Theory Heights  Heights Chart Lat Section exists form of mem chart Ring Z ebb960862da6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L70-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PChartLatSection.lean#L70-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_form_of_mem_chartRingZ_ebb960862da6 (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω} (hx : x ∈ Geo.chartRingZ (ι := blockIdx n) y c) :
    ∃ (δ : ι → ℕ) (e : MvPolynomial (Coord n) ℤ), IsWeightedHomogeneous (coordDeg n) e δ ∧
      aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartLatSection».«exists_form_of_mem_chartRingZ» := P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_form_of_mem_chartRingZ_ebb960862da6
