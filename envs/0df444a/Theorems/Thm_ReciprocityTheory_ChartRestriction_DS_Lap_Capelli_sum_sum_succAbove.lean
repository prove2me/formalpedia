-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_sum_sum_succAbove
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.sum_sum_succAbove
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:43.435181+00:00
-- url     : https://prove2.me/theorems/4d9d86b9-9108-59d0-a7e9-69c256da6a8f
-- title:
--   Capelli: sum sum succ Above
-- statement:
--   The Capelli construction uses the sum sum succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean#L55-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean#L55-L63

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.sum_sum_succAbove {M : Type*} [AddCommGroup M] {p : ℕ} (f : Fin (p + 1) → M) :
    ∑ i : Fin (p + 1), ∑ t : Fin p, f (i.succAbove t) = p • ∑ s, f s := by sorry
