-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_moment_fibre
-- name    : ReciprocityTheory.ChartRestriction.DS.moment_fibre
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:58:21.205833+00:00
-- url     : https://prove2.me/theorems/5fa48009-2b16-49cf-9752-153ae08d37fb
-- title:
--   DS: moment fibre
-- statement:
--   The DS construction uses the moment fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/MomentMatch.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/MomentMatch.lean#L22-L46

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

theorem ReciprocityTheory.ChartRestriction.DS.moment_fibre {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (p : ℂ) :
    ∑ i ∈ univ.filter (fun i => b i = p), u i = ∑ s ∈ univ.filter (fun s => a s = p), r s := by sorry
