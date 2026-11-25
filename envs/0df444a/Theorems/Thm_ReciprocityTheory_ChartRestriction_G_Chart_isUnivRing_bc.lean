-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isUnivRing_bc
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.isUnivRing_bc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:47:04.922698+00:00
-- url     : https://prove2.me/theorems/cee6ffd5-ed98-42bd-809e-5f994a7c87aa
-- title:
--   Chart: is Univ Ring bc
-- statement:
--   The Chart construction uses the is Univ Ring bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsUnivRingBc.lean#L33-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsUnivRingBc.lean#L33-L144

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] (eps : B →ₐ[R] R) {n : ℕ}
variable {R' : Type} [CommRing R'] [Algebra R R']

theorem ReciprocityTheory.ChartRestriction.G.Chart.isUnivRing_bc (m : ℕ) (π : B →ₐ[R] JetR R (Fin n) m) (hπ : IsUnivRing eps m π)
    (hπa : (jetAug R (Fin n) m).comp π = eps) (A : Type) [CommRing A] [Algebra R' A] [Algebra R A]
    [IsScalarTower R R' A] (aug : A →ₐ[R'] R') (hJ : (RingHom.ker aug) ^ (m + 1) = ⊥) (h : B →ₐ[R] A)
    (hh : (aug.restrictScalars R).comp h = (Algebra.ofId R R').comp eps) :
    ∃! ψ : JetR R' (Fin n) m →ₐ[R'] A,
      aug.comp ψ = jetAug R' (Fin n) m ∧ h = (ψ.restrictScalars R).comp ((jetMapA n m).comp π) := by sorry
