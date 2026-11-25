-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_resSeries_eq_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.resSeries_eq_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:53:46.079402+00:00
-- url     : https://prove2.me/theorems/46c5f09c-a8d3-4e63-95de-2d6bf7fab9ae
-- title:
--   DS: res Series eq sum
-- statement:
--   The DS construction uses the res Series eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L93-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L93-L108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
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

theorem ReciprocityTheory.ChartRestriction.DS.resSeries_eq_sum {n : ℕ} {a : Fin n → ℂ} (ha : Function.Injective a) :
    resSeries a = ∑ s, (∏ s' ∈ univ.erase s, (a s - a s' + 1) / (a s - a s')) •
      (PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) := by sorry
