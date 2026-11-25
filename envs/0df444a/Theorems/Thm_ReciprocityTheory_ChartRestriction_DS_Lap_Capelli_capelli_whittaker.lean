-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelli_whittaker
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelli_whittaker
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:34.754115+00:00
-- url     : https://prove2.me/theorems/48754a4d-cea3-528f-bf0c-da96ed33791a
-- title:
--   Capelli: capelli whittaker
-- statement:
--   The Capelli construction uses the capelli whittaker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L258-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L258-L284

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

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.capelli_whittaker (k r : ℕ) (E : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → Module.End ℂ M)
    (D : Fin k → Fin k → Module.End ℂ R) (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ)
    (l : M →ₗ[ℂ] R) (x : ℂ) (hE : IsGlRep E) (hr : 0 < r)
    (hl : ∀ a b, blk k r a < blk k r b → l ∘ₗ E a b = ψ a b • l)
    (hψ : ∀ a b, blk k r a < blk k r b → ¬ IsSimplePair k r a b → ψ a b = 0)
    (hD : ∀ i j, l ∘ₗ E (wIdx k r i) (wIdx k r j) = D i j ∘ₗ l) :
    l ∘ₗ cminor E Fin.castSucc Fin.succ x =
      ((-1) ^ k * kappa k r ψ) • (capelliC D (x - (r : ℂ)) ∘ₗ l) := by sorry
