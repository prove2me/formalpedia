-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isHolTo_of_local
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_local
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T14:56:57.528742+00:00
-- url     : https://prove2.me/theorems/2d48c714-adac-5b1e-b11f-ffe373fd119a
-- title:
--   Pullback Sections: is Hol To of local
-- statement:
--   The Pullback Sections construction uses the is Hol To of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPairA.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolPairA.lean#L34-L47

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_local {Y : Scheme.{0}} {B : Set V} {y : V → (Sp ℂ ⟶ Y)}
    (h : ∀ (U : Y.Opens) (f : Γ(Y, U)) (b₀ : V), b₀ ∈ B → ⊤ ≤ y b₀ ⁻¹ᵁ U →
      ∃ N ∈ nhds b₀, N ⊆ {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun b => valAt' (y b) U f) N) :
    IsHolTo B y := by sorry
