-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Mult1_Fold_cutFold
-- name    : ReciprocityTheory.ChartRestriction.DS.Mult1.Fold.cutFold
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:50.811423+00:00
-- url     : https://prove2.me/theorems/b2448289-ce93-4386-9bdd-91d2f7bc47a5
-- title:
--   Fold: cut Fold
-- statement:
--   The Fold construction uses the cut Fold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/CutFold.lean#L9-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/MultiplicityOne/CutFold.lean#L9-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_CutFold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

theorem ReciprocityTheory.ChartRestriction.DS.Mult1.Fold.cutFold {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (F G : β → α → α) (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (hmp : ∀ᵐ s ∂ν, μ.map (F s) = μ) (hinv : ∀ᵐ p ∂(ν.prod μ), G p.1 (F p.1 p.2) = p.2)
    (b : α → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (h1 : ∀ᵐ x ∂μ, Integrable (fun s => b (G s x)) ν ∧ ∫ s, b (G s x) ∂ν = 1)
    (φ : α → E) (hφ : Integrable φ μ) :
    Integrable (fun p : β × α => b p.2 • φ (F p.1 p.2)) (ν.prod μ) ∧
      ∫ x, φ x ∂μ = ∫ x, b x • ∫ s, φ (F s x) ∂ν ∂μ := by sorry
