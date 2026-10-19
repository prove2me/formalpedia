-- Prove2me | Theorems.Thm_TypeDensity_strict_transform_mapsTo_child_ideals
-- name    : TypeDensity.strict_transform_mapsTo_child_ideals
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:45:03.395183+00:00
-- url     : https://prove2.me/theorems/a23d93fa-03d4-4b1b-a0f1-1b9978d87f1f
-- title:
--   Proposition 5.1 (maps-to part): taking strict transforms at all exceptional points sends the fixed tangent cell of state `s` and degree `d` into the product of the child ideal sets.
-- statement:
--   Proposition 5.1 (maps-to part): taking strict transforms at all exceptional points sends the fixed tangent cell of state `s` and degree `d` into the product of the child ideal sets.
-- source:
--   TypeDensity/Blowup/StrictNormalizer.lean#L255-L340

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
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
import Theorems.Thm_TypeDensity_directionPoint_properties
import Theorems.Thm_TypeDensity_count_normalizedFactors_divisorAffinePolynomial
import Theorems.Thm_TypeDensity_infinity_point_maximal
import Theorems.Thm_TypeDensity_reduced_form_eq_of_residue_coeff
import Theorems.Thm_TypeDensity_concrete_infinity_boundary_contact
import Theorems.Thm_TypeDensity_concrete_zero_boundary_contact
import Theorems.Thm_TypeDensity_fixed_tangent_cell_generator_coefficients
import Theorems.Thm_TypeDensity_concrete_infinity_strict_transform_multiplicity
import Theorems.Thm_TypeDensity_concrete_strict_transform_generators
import Theorems.Thm_TypeDensity_concrete_strict_transform_multiplicity
import Theorems.Thm_TypeDensity_concrete_surface_parameterIdeal_isMaximal
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
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.strict_transform_mapsTo_child_ideals (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
    [IsDomain (ConcreteSurface O pi u a b)] [IsRegularLocalRing (ConcreteSurface O pi u a b)]
    (S : SurfaceData O (ConcreteSurface O pi u a b))
    (hS : S.t = (surfaceT O pi u a b) ∧ S.x = (surfaceX O pi u a b) ∧ S.a = a ∧ S.b = b)
    (e : ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸
    chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ≃+*
    Polynomial (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (he : ∀ r : (ConcreteSurface O pi u a b), e
    (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) r)) =
    Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk
    (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
    (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) =
    Polynomial.X) (Dv : ExceptionalDivisor (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (hinf : (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
    (surfaceX O pi u a b)).IsPrime) (s : State) (d : ℕ) :
    Set.MapsTo (fun J Q => divisorStrictTransform (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) e Dv hinf d J Q)
      (fixedTangentCell O (ConcreteSurface O pi u a b) S s d Dv)
      (Set.pi Set.univ
      (childIdealSet (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b) e Dv
      hinf s d)) := by sorry
