-- Prove2me | Theorems.Thm_TypeDensity_child_ideals_curve_datum
-- name    : TypeDensity.child_ideals_curve_datum
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:45:58.176314+00:00
-- url     : https://prove2.me/theorems/3ed58cb1-e63a-44da-9077-578a51a0e97b
-- title:
--   Every family of child ideals over the support of `Dv` is realized by a two-chart curve datum matching `Dv`: any global function with the prescribed chart strict transforms has strict transform `I Q` a
-- statement:
--   Every family of child ideals over the support of `Dv` is realized by a two-chart curve datum matching `Dv`: any global function with the prescribed chart strict transforms has strict transform `I Q` at every point `Q`.
-- source:
--   TypeDensity/Blowup/DivisorPoints.lean#L472-L526

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
import Theorems.Thm_TypeDensity_directionPoint_properties
import Theorems.Thm_TypeDensity_mul_injective_quotient_transport
import Theorems.Thm_TypeDensity_exists_pow_le_span_pair_transport
import Theorems.Thm_TypeDensity_map_maximalIdeal_localCompletion
import Theorems.Thm_TypeDensity_map_maximalIdeal_localCompletion_transport
import Theorems.Thm_TypeDensity_two_chart_common_multiplicity_eq
import Theorems.Thm_TypeDensity_direction_point_overlap_maximal
import Theorems.Thm_TypeDensity_infinity_point_maximal
import Theorems.Thm_TypeDensity_completed_point_transport_left
import Theorems.Thm_TypeDensity_completed_point_transport_right
import Theorems.Thm_TypeDensity_child_ideal_generator_transverse_finite
import Theorems.Thm_TypeDensity_concrete_surface_parameterIdeal_isMaximal
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
import Theorems.Thm_TypeDensity_concrete_surface_data_exists_unconditional
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

theorem TypeDensity.child_ideals_curve_datum (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (pi : O)
    (hpi : Irreducible pi) (u : (TwoSeries O)ˣ) (a b : ℕ) (ha : 0 < a)
        [IsLocalRing (ConcreteSurface O pi u a b)]
    (e : ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) ⧸ (chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ≃+* Polynomial (IsLocalRing.ResidueField
        (ConcreteSurface O pi u a b)))
    (he : ∀ r : ConcreteSurface O pi u a b, e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))
        ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) r)) = Polynomial.C (IsLocalRing.residue (ConcreteSurface O pi u a b) r))
    (heZ : e (Ideal.Quotient.mk ((chartExceptional (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) ((chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)))) = Polynomial.X)
    (Dv : ExceptionalDivisor (IsLocalRing.ResidueField (ConcreteSurface O pi u a b)))
    (hinf : (infinityPoint (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b)).IsPrime) (s : State) (d : ℕ)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b))
    (I : ∀ Q : divisorSupport Dv, Ideal (divisorLocalRing (ConcreteSurface O pi u a b)
        (surfaceT O pi u a b) (surfaceX O pi u a b) e Dv hinf Q))
    (hI : ∀ Q : divisorSupport Dv, I Q ∈ childIdealSet (ConcreteSurface O pi u a b)
        (surfaceT O pi u a b) (surfaceX O pi u a b) e Dv hinf s d Q) :
    ∃ D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
        beta, MatchesDivisor e D Dv ∧ ∀ f : ConcreteSurface O pi u a b,
      (∀ s : D.ι ⊕ D.ι0,
        strictTransformAt (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
            (leftPoint D s) d (Ideal.span {f}) = Ideal.span {leftData D s}) →
      (∀ s : D.ι ⊕ D.ιinf, strictTransformAt (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
          (surfaceT O pi u a b) (rightPoint D s) d (Ideal.span {f}) =
        Ideal.span {rightData D s}) →
      ∀ Q : divisorSupport Dv, divisorStrictTransform (ConcreteSurface O pi u a b)
          (surfaceT O pi u a b) (surfaceX O pi u a b) e Dv hinf d (Ideal.span {f}) Q =
        I Q := by sorry
