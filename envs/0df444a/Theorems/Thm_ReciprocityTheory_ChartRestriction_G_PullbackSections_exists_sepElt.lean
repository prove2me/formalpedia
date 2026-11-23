-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_exists_sepElt
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:25:31.243375+00:00
-- url     : https://prove2.me/theorems/475d483e-3366-4695-b84f-37676b5ef4e3
-- title:
--   Pullback Sections: exists sep Elt
-- statement:
--   The Pullback Sections construction uses the exists sep Elt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeC.lean#L9-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeC.lean#L9-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Polynomial NumberField IntermediateField Module

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt {E : Type} [Field E] [NumberField E] {F : Type} [Field F] (j : F →+* ℂ)
    (χ : (E →+* ℂ) → (𝓞 E →+* F)) (hχ : ∀ τ a, j (χ τ a) = τ (a : E)) :
    ∃ α : 𝓞 E, Function.Injective (fun τ => χ τ α) ∧
      (∃ f : ℤ[X], aeval α f = 0 ∧ f.map (Int.castRingHom F) = ∏ τ, (X - C (χ τ α))) ∧
      ∀ a : 𝓞 E, ∃ (N : ℤ) (g : ℤ[X]), N ≠ 0 ∧ (N : 𝓞 E) * a = aeval α g := by sorry
