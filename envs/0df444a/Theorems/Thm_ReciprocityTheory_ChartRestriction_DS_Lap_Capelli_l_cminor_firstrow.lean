-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_l_cminor_firstrow
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.l_cminor_firstrow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:39.069412+00:00
-- url     : https://prove2.me/theorems/3420b4fe-abc4-4765-8480-cdc6d4b98634
-- title:
--   Capelli: l cminor firstrow
-- statement:
--   The Capelli construction uses the l cminor firstrow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L34-L41

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.l_cminor_firstrow {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) (bl : Fin n → ℕ)
    (ψ : Fin n → Fin n → ℂ) (l : M →ₗ[ℂ] R) (hl : ∀ a b, bl a < bl b → l ∘ₗ E a b = ψ a b • l)
    {p : ℕ} (Rs Cs : Fin (p + 1) → Fin n) (x : ℂ) (hC : ∀ j, bl (Rs 0) < bl (Cs j)) :
    l ∘ₗ cminor E Rs Cs x = ∑ j : Fin (p + 1), ((-1 : ℂ) ^ (j : ℕ) * ψ (Rs 0) (Cs j)) •
      (l ∘ₗ cminor E (Rs ∘ Fin.succ) (Cs ∘ j.succAbove) x) := by sorry
