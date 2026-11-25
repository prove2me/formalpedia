-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_moment_poly
-- name    : ReciprocityTheory.ChartRestriction.DS.moment_poly
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:53:11.548959+00:00
-- url     : https://prove2.me/theorems/3683d0b8-8548-4f81-92ed-ce6bfd050eaf
-- title:
--   DS: moment poly
-- statement:
--   The DS construction uses the moment poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/MomentMatch.lean#L9-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/MomentMatch.lean#L9-L20

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

theorem ReciprocityTheory.ChartRestriction.DS.moment_poly {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (Q : ℂ[X]) :
    ∑ i, u i * Q.eval (b i) = ∑ s, r s * Q.eval (a s) := by sorry
