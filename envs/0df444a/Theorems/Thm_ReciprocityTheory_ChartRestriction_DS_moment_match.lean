-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_moment_match
-- name    : ReciprocityTheory.ChartRestriction.DS.moment_match
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:15.266443+00:00
-- url     : https://prove2.me/theorems/f1bc8baa-ed0f-4ea6-b381-8ee06894238d
-- title:
--   DS: moment match
-- statement:
--   The DS construction uses the moment match property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/MomentMatch.lean#L50-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/MomentMatch.lean#L50-L73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_MomentMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.moment_match {ι : Type*} [Fintype ι] (b : ι → ℂ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (a : Fin n → ℂ)
    (ha : Function.Injective a) (r : Fin n → ℂ)
    (h : ∀ k : ℕ, ∑ i, (w i : ℂ) * b i ^ k = ∑ s, r s * a s ^ k) :
    (∀ i, ∃ s, b i = a s) ∧ ∀ s, r s = ∑ i ∈ univ.filter (fun i => b i = a s), (w i : ℂ) := by sorry
