-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_l_entry
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_l_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:35.384089+00:00
-- url     : https://prove2.me/theorems/7272a16d-8d35-47c7-999a-34f4b7fcd672
-- title:
--   Capelli: wh B l entry
-- statement:
--   The Capelli construction uses the wh B l entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L17-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero
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
variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_l_entry {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (bl : Fin n → ℕ)
    (ψ : Fin n → Fin n → ℂ) (l : M →ₗ[ℂ] R) (hl : ∀ a b, bl a < bl b → l ∘ₗ E a b = ψ a b • l)
    {a b : Fin n} (h : bl a < bl b) (x : ℂ) (Y : Module.End ℂ M) :
    l ∘ₗ (capEntry E x a b * Y) = ψ a b • (l ∘ₗ Y) := by sorry
