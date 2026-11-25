-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_infinitesimalShift_reversed
-- name    : ReciprocityTheory.ChartRestriction.DS.infinitesimalShift_reversed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:23.536811+00:00
-- url     : https://prove2.me/theorems/ec90c915-1498-49db-ad17-13c8a563a698
-- title:
--   DS: infinitesimal Shift reversed
-- statement:
--   The DS construction uses the infinitesimal Shift reversed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L71-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean#L71-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.infinitesimalShift_reversed (ν : Fin n → ℝ) :
    icShift ((fun r => -ν (Fin.rev r)) + rho n) = icShift (-(ν + rho n)) ∘ Fin.revPerm := by sorry
