-- Prove2me | Theorems.Thm_TypeDensity_strict_transform_injOn_fixed_tangent_cell
-- name    : TypeDensity.strict_transform_injOn_fixed_tangent_cell
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T16:02:16.359192+00:00
-- url     : https://prove2.me/theorems/95d0236f-5c48-43a6-a054-f8b580abcfdc
-- title:
--   On the fixed tangent cell, an ideal is determined by its strict transforms at the points of the exceptional divisor `Dv`.
-- statement:
--   On the fixed tangent cell, an ideal is determined by its strict transforms at the points of the exceptional divisor `Dv`.
-- source:
--   TypeDensity/Blowup/FixedTangentCellBijection.lean#L354-L419

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
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Blowup_DivisorPoints
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Definitions.Def_TypeDensity_Recursion_Termination
import Theorems.Thm_TypeDensity_parent_ideal_unique_of_level_lattice
import Theorems.Thm_TypeDensity_fixed_tangent_cell_curve_datum
import Theorems.Thm_TypeDensity_concrete_two_chart_glued_generators_exist
import Theorems.Thm_TypeDensity_has_tangent_divisor_multiplicity
import Theorems.Thm_TypeDensity_actual_blowup_restriction_exists
import Theorems.Thm_TypeDensity_cell_strict_transforms_agree_at_datum_points
import Theorems.Thm_TypeDensity_strict_transforms_give_level_lattice_membership
import Theorems.Thm_TypeDensity_two_chart_left_generators_regular_on_overlap
import Theorems.Thm_TypeDensity_two_chart_datum_concrete_instances
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_tx
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_xt
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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.strict_transform_injOn_fixed_tangent_cell (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) [IsDomain (ConcreteSurface O pi u a b)]
        [IsRegularLocalRing (ConcreteSurface O pi u a b)] (S : SurfaceData O
            (ConcreteSurface O pi u a b))
    (hS : S.t = surfaceT O pi u a b ∧ S.x = surfaceX O pi u a b ∧ S.a = a ∧ S.b = b)
    (e : ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸ (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ≃+* Polynomial (IsLocalRing.ResidueField
        (ConcreteSurface O pi u a b)))
    (he : ∀ r : ConcreteSurface O pi u a b, e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))
        ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) r)) = Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) = Polynomial.X)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (hinf : (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)).IsPrime) (s : State) (d : ℕ)
    (hdeg : exceptionalDegree (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)) Dv = d) :
    Set.InjOn (fun J Q => divisorStrictTransform (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b) e Dv hinf d J Q)
      (fixedTangentCell O (ConcreteSurface O pi u a b) S s d Dv) := by sorry
