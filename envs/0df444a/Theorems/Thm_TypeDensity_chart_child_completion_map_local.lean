-- Prove2me | Theorems.Thm_TypeDensity_chart_child_completion_map_local
-- name    : TypeDensity.chart_child_completion_map_local
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:17.859737+00:00
-- url     : https://prove2.me/theorems/489b4858-2b56-4d1c-bda3-e8211433380a
-- title:
--   The extension `Λ'` of `chart_child_completion_map_exists` is local: the maximal ideal of the completion is exactly the preimage of the parameter ideal.
-- statement:
--   The extension `Λ'` of `chart_child_completion_map_exists` is local: the maximal ideal of the completion is exactly the preimage of the parameter ideal.
-- source:
--   TypeDensity/Surfaces/Regularity.lean#L175-L208

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Blowup_Charts
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_concrete_surface_maximalIdeal_eq
import Theorems.Thm_TypeDensity_concrete_surface_isLocalRing
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PicardGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.chart_child_completion_map_local (A : Type) [CommRing A] [IsNoetherianRing A] (O' : Type)
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] (pi' : O') (hpi' : Irreducible pi')
    (u' : (TwoSeries O')ˣ) (a' b' : ℕ) (ha' : 0 < a') (Λ : A →+* ConcreteSurface O' pi' u' a' b')
    (P : Ideal A) [P.IsPrime] (hP : ∀ x : A, x ∈ P ↔ Λ x ∈ surfaceParameterIdeal O' pi' u' a' b')
    (Λ' : CompletedLocalAt A P →+* ConcreteSurface O' pi' u' a' b')
    (hΛ' : ∀ x : A, Λ' (completedPointMap A P x) = Λ x) :
    ∀ y : CompletedLocalAt A P,
      y ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (localCompletionMap (Localization.AtPrime P)) ↔
      Λ' y ∈ surfaceParameterIdeal O' pi' u' a' b' := by sorry
