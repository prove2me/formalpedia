-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_resSeries_coeff_succ
-- name    : ReciprocityTheory.ChartRestriction.DS.resSeries_coeff_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:33.91898+00:00
-- url     : https://prove2.me/theorems/ca96a85e-2629-4fc1-bc3e-0840c46ab10b
-- title:
--   DS: res Series coeff succ
-- statement:
--   The DS construction uses the res Series coeff succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L141-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L141-L144

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

theorem ReciprocityTheory.ChartRestriction.DS.resSeries_coeff_succ {a : Fin n → ℂ} (ha : Function.Injective a) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries a) = ∑ s, resid a s * a s ^ k := by sorry
