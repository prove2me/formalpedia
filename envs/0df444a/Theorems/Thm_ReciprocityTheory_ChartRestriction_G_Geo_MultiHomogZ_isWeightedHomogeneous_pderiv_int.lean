-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_MultiHomogZ_isWeightedHomogeneous_pderiv_int
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ.isWeightedHomogeneous_pderiv_int
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:51.2448+00:00
-- url     : https://prove2.me/theorems/30fab876-56db-5e6d-8395-69898622e54b
-- title:
--   Multi Homog Z: is Weighted Homogeneous pderiv int
-- statement:
--   The Multi Homog Z construction uses the is Weighted Homogeneous pderiv int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterMinorA.lean#L43-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterMinorA.lean#L43-L55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinorA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.Geo.MultiHomogZ.isWeightedHomogeneous_pderiv_int {σ : Type*} {w : σ → ℤ} {f : MvPolynomial σ R} {d : ℤ}
    (h : IsWeightedHomogeneous w f d) (q : σ) :
    IsWeightedHomogeneous w (pderiv q f) (d - w q) := by sorry
