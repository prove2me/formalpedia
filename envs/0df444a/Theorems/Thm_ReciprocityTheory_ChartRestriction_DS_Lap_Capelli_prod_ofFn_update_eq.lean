-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_prod_ofFn_update_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.prod_ofFn_update_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:43:11.562496+00:00
-- url     : https://prove2.me/theorems/e9851bb4-775e-5c96-9475-c4abcaad08ba
-- title:
--   Capelli: prod of Fn update eq
-- statement:
--   The Capelli construction uses the prod of Fn update eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ProdOfFnUpdateEq.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ProdOfFnUpdateEq.lean#L15-L32

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
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
variable {𝒰 : Type*} [Ring 𝒰]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.prod_ofFn_update_eq {p : ℕ} (f : Fin p → 𝒰) (j : Fin p) :
    ∃ A B : 𝒰, ∀ v, (List.ofFn (Function.update f j v)).prod = A * v * B := by sorry
