-- Prove2me | Theorems.Thm_TypeDensity_two_chart_datum_concrete_transverse
-- name    : TypeDensity.two_chart_datum_concrete_transverse
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:32:03.457297+00:00
-- url     : https://prove2.me/theorems/d32f3d2d-b633-4322-96b4-58f15422d50e
-- title:
--   The strict transforms in two-chart curve data on the blow-up of the concrete surface are transverse to the exceptional divisor at every point.
-- statement:
--   The strict transforms in two-chart curve data on the blow-up of the concrete surface are transverse to the exceptional divisor at every point.
-- source:
--   TypeDensity/Surfaces/ConcreteStrictTransforms.lean#L365-L426

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
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Theorems.Thm_TypeDensity_beta_right_chartBase_self
import Theorems.Thm_TypeDensity_two_chart_left_data_transverse_finite
import Theorems.Thm_TypeDensity_two_chart_left_points_maximal
import Theorems.Thm_TypeDensity_two_chart_right_data_transverse_finite
import Theorems.Thm_TypeDensity_two_chart_right_points_maximal
import Theorems.Thm_TypeDensity_concrete_surface_quotient_T_equiv
import Theorems.Thm_TypeDensity_concrete_left_point_completion_is_surface
import Theorems.Thm_TypeDensity_concrete_infinity_point_completion
import Theorems.Thm_TypeDensity_concrete_surface_isNoetherianRing
import Theorems.Thm_TypeDensity_concrete_surface_equiv_curve_length_and_regular
import Theorems.Thm_TypeDensity_concrete_surface_parameterIdeal_isMaximal
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
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.two_chart_datum_concrete_transverse (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a)
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b))
    (D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) beta) :
    (∀ s : D.ι ⊕ D.ι0,
        Function.Injective
        (fun w : (CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) (leftPoint D s)) ⧸ Ideal.span
          {(completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) (leftPoint D s))
            ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceT O pi u a b))} =>
          Ideal.Quotient.mk (Ideal.span {(completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))) (leftPoint D s))
            ((chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)) (surfaceT O pi u a b))}) (leftData D s) * w)) ∧
      ∀ s : D.ι ⊕ D.ιinf,
      Function.Injective
      (fun w : (CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (rightPoint D s)) ⧸ Ideal.span
        {(completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (rightPoint D s))
          ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) (surfaceX O pi u a b))} =>
        Ideal.Quotient.mk (Ideal.span {(completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (rightPoint D s))
          ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) (surfaceX O pi u a b))}) (rightData D s) * w) := by sorry
