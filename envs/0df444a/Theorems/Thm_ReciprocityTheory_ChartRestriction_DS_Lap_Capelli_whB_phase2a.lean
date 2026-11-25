-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_whB_phase2a
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_phase2a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:44:43.811058+00:00
-- url     : https://prove2.me/theorems/3578187d-9a6a-55d3-9870-c3ec8d4390d6
-- title:
--   Capelli: wh B phase2a
-- statement:
--   The Capelli construction uses the wh B phase2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L178-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/CapelliWhittakerZero.lean#L178-L222

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
variable (k r : ℕ) (E : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → Module.End ℂ M)
  (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) (l : M →ₗ[ℂ] R) (hE : IsGlRep E)
  (hl : ∀ a b, blk k r a < blk k r b → l ∘ₗ E a b = ψ a b • l)
  (hψ : ∀ a b, blk k r a < blk k r b → ¬ IsSimplePair k r a b → ψ a b = 0)
include hE hl hψ

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_phase2a (j : ℕ) : ∀ (s : ℕ), s + j + 1 = r → ∀ y : ℂ,
    l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) s (k + j + 1)) (whB_seg (k + 2 * r + 1) (s + 1) (k + j + 1)) y =
      (∏ i ∈ range j, whB_g k r ψ (whB_c (k + 2 * r + 1) (s + i))) •
        (l ∘ₗ cminor E (whB_seg (k + 2 * r + 1) (r - 1) (k + 1)) (whB_seg (k + 2 * r + 1) r (k + 1)) y) := by sorry
