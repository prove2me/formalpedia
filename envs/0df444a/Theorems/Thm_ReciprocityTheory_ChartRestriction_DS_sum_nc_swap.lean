-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sum_nc_swap
-- name    : ReciprocityTheory.ChartRestriction.DS.sum_nc_swap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:56:48.540746+00:00
-- url     : https://prove2.me/theorems/5a9ba46a-3284-4d19-aa2d-5290de06e387
-- title:
--   DS: sum nc swap
-- statement:
--   The DS construction uses the sum nc swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/NcBound.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/NcBound.lean#L27-L35

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

theorem ReciprocityTheory.ChartRestriction.DS.sum_nc_swap (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), f b a =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε a ≠ ε b), f a b := by sorry
