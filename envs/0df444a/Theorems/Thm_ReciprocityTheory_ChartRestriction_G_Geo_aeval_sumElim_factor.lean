-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_aeval_sumElim_factor
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.aeval_sumElim_factor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:23:08.060991+00:00
-- url     : https://prove2.me/theorems/39ea7318-ac48-45cb-aed7-aa62f17658e1
-- title:
--   Geo: aeval sum Elim factor
-- statement:
--   The Geo construction uses the aeval sum Elim factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L133-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodF.lean#L133-L148

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (k0 : K)

theorem ReciprocityTheory.ChartRestriction.G.Geo.aeval_sumElim_factor {S : Type*} [CommRing S] [Algebra ℚ S] {r : ℕ}
    {H : MvPolynomial (Fin r ⊕ {k // k ≠ k0}) ℚ} {δ : K →₀ ℕ}
    (hH : IsWeightedHomogeneous (sWt k0 r) H δ) {n0 : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ}
    (hn0 : n0 ∈ H.support) (a : Fin r → S) (b : {k // k ≠ k0} → S) :
    aeval (Sum.elim a b) H = (∏ k', b k' ^ n0 (Sum.inr k')) * aeval (Sum.elim a 1) H := by sorry
