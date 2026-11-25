-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_update_col
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_update_col
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:42:17.726632+00:00
-- url     : https://prove2.me/theorems/eeccb8e9-744f-47e3-b95e-9a97f9ac56c9
-- title:
--   Capelli: cminor update col
-- statement:
--   The Capelli construction uses the cminor update col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean#L91-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean#L91-L101

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
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_update_col (hE : GlRelR E) {p : ℕ} (R : Fin p → Fin n) (C : Fin (p + 1) → Fin n)
    (j : Fin (p + 1)) (t : Fin p) (y : ℂ) :
    cminor E R (Function.update (C ∘ j.succAbove) t (C j)) y =
      ((-1 : ℂ) ^ ((j : ℕ) + (j.succAbove t : ℕ) + 1)) • cminor E R (C ∘ (j.succAbove t).succAbove) y := by sorry
