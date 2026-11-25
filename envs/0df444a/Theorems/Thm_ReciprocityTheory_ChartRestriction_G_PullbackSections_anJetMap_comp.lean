-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anJetMap_comp
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.anJetMap_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T17:43:22.44518+00:00
-- url     : https://prove2.me/theorems/5171c2fb-6566-5e33-84c8-4a39b46bf8fd
-- title:
--   Pullback Sections: an Jet Map comp
-- statement:
--   The Pullback Sections construction uses the an Jet Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L125-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/AnHolFamOfHolTo.lean#L125-L136

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
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
open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
variable {Y : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.anJetMap_comp {K : Type} [Field K] {Ia Ib Ic : Type} {m : ℕ} (φ : Ia → MvPolynomial Ib K)
    (hφ : ∀ i, φ i ∈ orig K Ib) (ψ : Ib → MvPolynomial Ic K) (hψ : ∀ i, ψ i ∈ orig K Ic)
    (ch : Ia → MvPolynomial Ic K) (hch : ∀ i, ch i ∈ orig K Ic) (h : ∀ i, MvPolynomial.aeval ψ (φ i) = ch i)
    (a : Jet K Ia m) : jetMap ψ hψ (jetMap φ hφ a) = jetMap ch hch a := by sorry
