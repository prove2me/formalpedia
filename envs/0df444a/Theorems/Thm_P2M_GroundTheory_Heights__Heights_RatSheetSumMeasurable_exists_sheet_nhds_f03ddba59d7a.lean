-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_exists_sheet_nhds_f03ddba59d7a
-- name    : P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_exists_sheet_nhds_f03ddba59d7a
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:16:40.760988+00:00
-- url     : https://prove2.me/theorems/66c94de4-cee4-4a70-b5d5-6d555ee2b18a
-- title:
--   P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable exists sheet nhds f03ddba59d7a: P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable exists sheet nhds f03ddba59d7a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable exists sheet nhds f03ddba59d7a construction uses the P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable exists sheet nhds f03ddba59d7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetSumMeasurable.lean#L46-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetSumMeasurable.lean#L46-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetSumMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_exists_sheet_nhds_e78e98ed3372

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ComplexSets
open GroundTheory.Heights₂.Heights.RatSheetSumMeasurable
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_exists_sheet_nhds_f03ddba59d7a {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ ContinuousOn s U ∧
      (∀ y ∈ U, s y ∈ zeroSet J ∧ eval (s y) q ≠ 0 ∧ RatChart.ratMap p q (s y) = y) ∧
      (∀ x' ∈ zeroSet J ∩ W, RatChart.ratMap p q x' ∈ U ∧ RatChart.IsRatSheetAt J p q x' s) ∧
      ((∃ s, RatChart.IsRatSheetAt J p q x s) → x ∈ W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatSheetSumMeasurable».«exists_sheet_nhds» := P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_exists_sheet_nhds_f03ddba59d7a
