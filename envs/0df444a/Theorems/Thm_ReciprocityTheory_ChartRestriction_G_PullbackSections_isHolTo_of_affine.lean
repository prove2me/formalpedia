-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolTo_of_affine
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_affine
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:27.852188+00:00
-- url     : https://prove2.me/theorems/312b6e92-c401-4cf8-9939-d2be6215f562
-- title:
--   Pullback Sections: is Hol To of affine
-- statement:
--   The Pullback Sections construction uses the is Hol To of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPairA.lean#L49-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPairA.lean#L49-L87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairA
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
open AlgebraicGeometry CategoryTheory Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_affine {T : Scheme.{0}} [IsAffine T] {B : Set V} (hB : IsOpen B) {z : V → (Sp ℂ ⟶ T)}
    (hz : ∀ r : Γ(T, ⊤), DifferentiableOn ℂ (fun b => valAt' (z b) ⊤ r) B) : IsHolTo B z := by sorry
