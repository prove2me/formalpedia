-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_resSeries_coeff_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.resSeries_coeff_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:01.23925+00:00
-- url     : https://prove2.me/theorems/e12396c5-23b3-46d7-9bbd-42822ee0bb69
-- title:
--   DS: res Series coeff zero
-- statement:
--   The DS construction uses the res Series coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L138-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L138-L139

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

theorem ReciprocityTheory.ChartRestriction.DS.resSeries_coeff_zero (a : Fin n → ℂ) : PowerSeries.coeff 0 (resSeries a) = 0 := by sorry
