-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_term_eq_b7600c1a566d
-- name    : P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_term_eq_b7600c1a566d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:16:14.586869+00:00
-- url     : https://prove2.me/theorems/556ad448-7a48-4637-9cec-cf6694974bc0
-- title:
--   P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable term eq b7600c1a566d: P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable term eq b7600c1a566d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable term eq b7600c1a566d construction uses the P2 M Ground Theory Heights  Heights Rat Sheet Sum Measurable term eq b7600c1a566d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetSumMeasurable.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetSumMeasurable.lean#L37-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetSumMeasurable
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_term_eq_ead537038306

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

theorem P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_term_eq_b7600c1a566d {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (Φ : ℝ → ℝ → ℝ) (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : RatChart.IsRatSheetAt J p q x s)
    (h : ∃ s, RatChart.IsRatSheetAt J p q x s) :
    Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) (RatChart.ratMap p q x)) =
      Φ (g x) (ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (RatChart.ratMap p q x)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatSheetSumMeasurable».«term_eq» := P2M_GroundTheory_Heights__Heights_RatSheetSumMeasurable_term_eq_b7600c1a566d
