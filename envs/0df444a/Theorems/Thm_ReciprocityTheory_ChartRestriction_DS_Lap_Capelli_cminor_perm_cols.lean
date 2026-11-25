-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_cminor_perm_cols
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_perm_cols
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:39.840041+00:00
-- url     : https://prove2.me/theorems/202394b5-6590-4e29-a03f-d8810ff28574
-- title:
--   Capelli: cminor perm cols
-- statement:
--   The Capelli construction uses the cminor perm cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ColAnti.lean#L133-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/ColAnti.lean#L133-L173

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.cminor_perm_cols (hE : GlRelR E) {p : ℕ} (R C : Fin p → Fin n) (τ : Equiv.Perm (Fin p))
    (x : ℂ) : cminor E R (C ∘ τ) x = ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • cminor E R C x := by sorry
