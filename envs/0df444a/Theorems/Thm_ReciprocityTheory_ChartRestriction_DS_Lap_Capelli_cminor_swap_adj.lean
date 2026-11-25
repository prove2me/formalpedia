-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_swap_adj
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_swap_adj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:42:32.454811+00:00
-- url     : https://prove2.me/theorems/0ef6ab0d-b55e-4566-b7ef-e3afe623394e
-- title:
--   Capelli: cminor swap adj
-- statement:
--   The Capelli construction uses the cminor swap adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ColAnti.lean#L92-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ColAnti.lean#L92-L131

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ColAnti
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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_swap_adj (hE : GlRelR E) {p : ℕ} (R C : Fin (p + 1) → Fin n) (j : Fin p) (x : ℂ) :
    cminor E R (C ∘ Equiv.swap j.castSucc j.succ) x = -cminor E R C x := by sorry
