-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_holPair
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:25:18.12674+00:00
-- url     : https://prove2.me/theorems/49715c3e-8f37-4efc-b2b6-e6d1f92462be
-- title:
--   Pullback Sections: hol Pair
-- statement:
--   The Pullback Sections construction uses the hol Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPair.lean#L33-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPair.lean#L33-L112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.holPair (X Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (n : ℕ) (B : Set (Fin n → ℂ))
    (e₁ : (Fin n → ℂ) → (Sp ℂ ⟶ Y₁)) (e₂ : (Fin n → ℂ) → (Sp ℂ ⟶ Y₂)) (he : ∀ b, e₁ b ≫ p₁ = e₂ b ≫ p₂) :
    IsOpen B → IsHolTo B e₁ → IsHolTo B e₂ → IsHolTo B (fun b => pullback.lift (e₁ b) (e₂ b) (he b)) := by sorry
