-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_exists_sum_nc_norm_sq_le
-- name    : ReciprocityTheory.ChartRestriction.DS.exists_sum_nc_norm_sq_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T09:54:36.331301+00:00
-- url     : https://prove2.me/theorems/182831a7-0a03-52d6-863b-1d2a53c4cd59
-- title:
--   DS: exists sum nc norm sq le
-- statement:
--   The DS construction uses the exists sum nc norm sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/NcBound.lean#L85-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/NcBound.lean#L85-L96

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_WeightBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_NcBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.exists_sum_nc_norm_sq_le (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M} (hVf : FiniteDimensional ℂ V) (hVK : IsKStableSub ε E V) {c : ℝ}
    (hc : ∀ v ∈ V, casimir E v = (c : ℂ) • v) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k : ℕ, ∀ x ∈ layer ε E V k,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 ≤
        ((R + √2 * k) ^ 2 - nsq (rhoC ε) - c) * ‖x‖ ^ 2 := by sorry
