-- Prove2me | Theorems.Thm_TypeDensity_chart_child_completion_equiv
-- name    : TypeDensity.chart_child_completion_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:53:31.420309+00:00
-- url     : https://prove2.me/theorems/ffa8b724-7ce9-4c01-87da-596a6363a51e
-- title:
--   Let `Λ : R[f/e] → R'` be a chart map to a concrete surface `R'` over `O'`, compatible with a substitution `s : O[[T,X]] → O'[[T,X]]` (`E ↦ T`, `F ↦ T (X + α)`), and surjective modulo the parameter ide
-- statement:
--   Let `Λ : R[f/e] → R'` be a chart map to a concrete surface `R'` over `O'`, compatible with a substitution `s : O[[T,X]] → O'[[T,X]]` (`E ↦ T`, `F ↦ T (X + α)`), and surjective modulo the parameter ideal. Then the completion of `R[f/e]` at `P = Λ⁻¹(t', x')` is isomorphic to `R'`.
-- source:
--   TypeDensity/Surfaces/ChartCompletions.lean#L97-L204

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_blowup_chart_ringHom_ext
import Theorems.Thm_TypeDensity_concrete_surface_ringHom_ext_of_isNilpotent
import Theorems.Thm_TypeDensity_twoSeries_eval_exists_of_isAdicComplete
import Theorems.Thm_TypeDensity_concrete_surface_isAdicComplete_maximalIdeal
import Theorems.Thm_TypeDensity_chart_point_isMaximal_of_residue_surjective
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
import Theorems.Thm_TypeDensity_concrete_surface_isLocalRing
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
import Theorems.Thm_TypeDensity_chart_child_completion_map_local
import Theorems.Thm_TypeDensity_child_series_eval_comp_chart_subst
import Theorems.Thm_TypeDensity_finite_completed_point_quotient_surjective
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.chart_child_completion_equiv (O O' : Type) [CommRing O] [IsNoetherianRing O] [CommRing O']
    [IsDomain O'] [IsDiscreteValuationRing O'] (pi : O) (u : (TwoSeries O)ˣ) (a b : ℕ) (pi' : O')
    (hpi' : Irreducible pi') (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a') (E F : TwoSeries O)
    (hEF : (E = axisT O ∧ F = axisX O) ∨ (E = axisX O ∧ F = axisT O)) (ρ : O →+* O') (α : O')
    (s : TwoSeries O →+* TwoSeries O')
    (hsC : ∀ c : O, s (MvPowerSeries.C c) = MvPowerSeries.C (ρ c)) (hsE : s E = axisT O')
    (hsF : s F = axisT O' * (axisX O' + MvPowerSeries.C α))
    (hs : s (surfaceRelation O pi u a b) = surfaceRelation O' pi' u' a' b')
    (Λ : (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) →+* ConcreteSurface O' pi' u' a' b')
    (hΛ : ∀ g : TwoSeries O, Λ ((chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) (surfaceMk O pi u a b g)) =
        surfaceMk O' pi' u' a' b' (s g))
    (hΛZ : Λ ((chartSlope (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) = surfaceX O' pi' u' a' b' + algebraMap O'
        (ConcreteSurface O' pi' u' a' b') α)
    (P : Ideal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)))) [P.IsPrime] (hP : ∀ x, x ∈ P ↔ Λ x ∈ surfaceParameterIdeal
        O' pi' u' a' b')
    (hsurj : ∀ y : ConcreteSurface O' pi' u' a' b', ∃ x : (BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)),
      Λ x - y ∈ surfaceParameterIdeal O' pi' u' a' b')
    (Λ' : CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) P →+* ConcreteSurface O' pi' u' a' b')
    (hΛ' : ∀ x, Λ' (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) P x) = Λ x)
        (κ : O' →+* CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) P)
    (hκ : ∀ c : O', Λ' (κ c) = algebraMap O' (ConcreteSurface O' pi' u' a' b') c)
    (hκρ : ∀ c : O,
      κ (ρ c) = completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) P
      ((chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) (algebraMap O (ConcreteSurface O pi u a b) c))) :
    ∃ Eq : CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) P ≃+* ConcreteSurface O' pi' u' a' b',
      (∀ y, Eq y = Λ' y) ∧ ∀ c : O',
      Eq.symm (algebraMap O' (ConcreteSurface O' pi' u' a' b') c) = κ c := by sorry
