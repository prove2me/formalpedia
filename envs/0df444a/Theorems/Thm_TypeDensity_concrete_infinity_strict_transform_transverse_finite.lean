-- Prove2me | Theorems.Thm_TypeDensity_concrete_infinity_strict_transform_transverse_finite
-- name    : TypeDensity.concrete_infinity_strict_transform_transverse_finite
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:31:45.552914+00:00
-- url     : https://prove2.me/theorems/23da7d13-fe44-42bb-9564-b534641c03a1
-- title:
--   At the point at infinity of the `x`-chart, the strict transform `∑ cᵢ (t/x)^(d-i)` of a curve `f = ∑ cᵢ t^(d-i) x^i` (some `cᵢ` a unit) and the exceptional equation `x` form a transverse pair, and the
-- statement:
--   At the point at infinity of the `x`-chart, the strict transform `∑ cᵢ (t/x)^(d-i)` of a curve `f = ∑ cᵢ t^(d-i) x^i` (some `cᵢ` a unit) and the exceptional equation `x` form a transverse pair, and they cut out a finite-length quotient.
-- source:
--   TypeDensity/Surfaces/ConcretePoints.lean#L340-L431

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
import Theorems.Thm_TypeDensity_x_chart_infinity_completion_equiv
import Theorems.Thm_TypeDensity_concrete_surface_quotient_T_equiv
import Theorems.Thm_TypeDensity_transverse_of_reduction_ne_zero
import Theorems.Thm_TypeDensity_concrete_infinity_point_completion
import Theorems.Thm_TypeDensity_residueKillT_xChartSubst
import Theorems.Thm_TypeDensity_chartSubst_apply_generators
import Theorems.Thm_TypeDensity_residueKillT_apply_ker
import Theorems.Thm_TypeDensity_concrete_surface_quotient_parameters_equiv
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

theorem TypeDensity.concrete_infinity_strict_transform_transverse_finite (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (d : ℕ)
    (c : Fin (d + 1) → ConcreteSurface O pi u a b)
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {(surfaceT O pi u a b), (surfaceX O pi u a b)})
    (P : Ideal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)))) [P.IsMaximal] [P.IsPrime]
    (hx : (chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) (surfaceX O pi u a b) ∈ P) (hW : (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) ∈ P) :
    Function.Injective
      (fun w : CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) P ⧸ Ideal.span
          {completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) P (∑ i : Fin (d+1),
            algebraMap (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (c i) *
              (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) ^ (d - i.val))} =>
        Ideal.Quotient.mk (Ideal.span {completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) P (∑ i : Fin (d+1),
            algebraMap (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (c i) *
              (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) ^ (d - i.val))})
          (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) P ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) (surfaceX O pi u a b))) * w) ∧
    Function.Injective
      (fun w : CompletedLocalAt ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) P ⧸ Ideal.span
          {completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) P ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) (surfaceX O pi u a b))} =>
        Ideal.Quotient.mk (Ideal.span
            {completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) P ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) (surfaceX O pi u a b))})
          (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) P (∑ i : Fin (d+1),
            algebraMap (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (c i) *
              (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) ^ (d - i.val))) * w) ∧
    ∃ L : ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
        (localCompletionMap (Localization.AtPrime P)))^L ≤
      finiteLocalCurveIdeal ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) P ((chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) (surfaceX O pi u a b))
        (completedPointMap ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) P (∑ i : Fin (d+1),
          algebraMap (ConcreteSurface O pi u a b) ((BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))) (c i) *
            (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)) ^ (d - i.val))) 1 := by sorry
