-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capEntry_comm
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capEntry_comm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:42:03.827801+00:00
-- url     : https://prove2.me/theorems/f08e4292-1c73-43d8-b931-9c1ec0dfb05c
-- title:
--   Capelli: cap Entry comm
-- statement:
--   The Capelli construction uses the cap Entry comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ProdOfFnUpdateEq.lean#L64-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ProdOfFnUpdateEq.lean#L64-L83

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
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capEntry_comm (hE : GlRelR E) (a b c d : Fin n) (x : ℂ) :
    E a b * capEntry E x c d - capEntry E x c d * E a b =
      (if b = c then capEntry E x a d else 0) - (if d = a then capEntry E x c b else 0) := by sorry
