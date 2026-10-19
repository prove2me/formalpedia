-- Prove2me | Theorems.Thm_TypeDensity_rational_point_completion_equiv
-- name    : TypeDensity.rational_point_completion_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:48.45861+00:00
-- url     : https://prove2.me/theorems/7108e35c-bd89-4227-8c3f-d2a64913ba92
-- title:
--   Common form of the completion isomorphisms at the rational points of the exceptional divisor: if `s : O[[T,X]] → O[[T,X]]` fixes constants, sends `E ↦ T`, `F ↦ T (X + α)` and the relation to a child r
-- statement:
--   Common form of the completion isomorphisms at the rational points of the exceptional divisor: if `s : O[[T,X]] → O[[T,X]]` fixes constants, sends `E ↦ T`, `F ↦ T (X + α)` and the relation to a child relation, then the completed local ring of `R[f/e]` at `P = (e, f/e - α)` is isomorphic to the child surface, compatibly with `s`.
-- source:
--   TypeDensity/Surfaces/ChartCompletions.lean#L728-L795

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
import Theorems.Thm_TypeDensity_chart_child_completion_equiv
import Theorems.Thm_TypeDensity_chart_child_map_exists
import Theorems.Thm_TypeDensity_chart_point_quotient_adjoinRoot_equiv
import Theorems.Thm_TypeDensity_concrete_surface_sub_constantCoeff_mem_parameterIdeal
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
import Theorems.Thm_TypeDensity_concrete_surface_isLocalRing
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
import Theorems.Thm_TypeDensity_chart_child_completion_map_exists
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

theorem TypeDensity.rational_point_completion_equiv (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ)
    (u' : (TwoSeries O)ˣ) (a' b' : ℕ) (ha' : 0 < a') (E F : TwoSeries O)
    (hEF : (E = axisT O ∧ F = axisX O) ∨ (E = axisX O ∧ F = axisT O))
    (hEFmax : (Ideal.span ({surfaceMk O pi u a b E, surfaceMk O pi u a b F} :
      Set (ConcreteSurface O pi u a b))).IsMaximal)
    (α : O) (s : TwoSeries O →+* TwoSeries O)
    (hsC : ∀ c : O, s (MvPowerSeries.C c) = MvPowerSeries.C c) (hsE : s E = axisT O)
    (hsF : s F = axisT O * (axisX O + MvPowerSeries.C α))
    (hrel : s (surfaceRelation O pi u a b) = surfaceRelation O pi u' a' b')
    (P : Ideal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)))) (hPp : P.IsPrime)
    (hP : P = Ideal.span {(chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) (surfaceMk O pi u a b E),
      (chartSlope (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) - (chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) (algebraMap O (ConcreteSurface O pi u a b)
          α)}) :
    ∃ Eq : CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) P ≃+* ConcreteSurface O pi u' a' b',
      (∀ g : TwoSeries O, Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) P
          ((chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)) (surfaceMk O pi u a b g))) =
        surfaceMk O pi u' a' b' (s g)) ∧
      Eq (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) P ((chartSlope (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F)))) =
        surfaceX O pi u' a' b' + algebraMap O (ConcreteSurface O pi u' a' b') α ∧
      ∀ c : O, Eq
        (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))) P ((chartBase (ConcreteSurface O pi u a b) (surfaceMk O pi u a b E) (surfaceMk O pi u a b F))
            (algebraMap O (ConcreteSurface O pi u a b) c))) =
        algebraMap O (ConcreteSurface O pi u' a' b') c := by sorry
