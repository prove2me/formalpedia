-- Prove2me | Theorems.Thm_TypeDensity_curve_datum_of_parent_function
-- name    : TypeDensity.curve_datum_of_parent_function
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:46:00.400693+00:00
-- url     : https://prove2.me/theorems/390b0aa3-8d4f-43ac-8db5-31812bb00812
-- title:
--   A form `f = ∑ cᵢ t^(d-i) x^i` on the concrete surface with some `cᵢ` a unit yields two-chart curve data: its strict transforms on the two blow-up charts, located at finitely many points of the excepti
-- statement:
--   A form `f = ∑ cᵢ t^(d-i) x^i` on the concrete surface with some `cᵢ` a unit yields two-chart curve data: its strict transforms on the two blow-up charts, located at finitely many points of the exceptional divisor.
-- source:
--   TypeDensity/Surfaces/ConcreteAtlas.lean#L651-L720

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
import Theorems.Thm_TypeDensity_blowup_chart_relation
import Theorems.Thm_TypeDensity_blowup_exceptional_parameter_regular
import Theorems.Thm_TypeDensity_exceptional_line_equiv_chart_exceptional
import Theorems.Thm_TypeDensity_mul_injective_quotient_transport
import Theorems.Thm_TypeDensity_exists_pow_le_span_pair_transport
import Theorems.Thm_TypeDensity_map_maximalIdeal_localCompletion
import Theorems.Thm_TypeDensity_map_maximalIdeal_localCompletion_transport
import Theorems.Thm_TypeDensity_blowup_chart_exceptional_point_polynomial
import Theorems.Thm_TypeDensity_nonzerodivisor_survives_localization
import Theorems.Thm_TypeDensity_blowup_overlap_isLocalization_right
import Theorems.Thm_TypeDensity_overlap_exceptional_point_comap_maximal
import Theorems.Thm_TypeDensity_completed_point_transport_left
import Theorems.Thm_TypeDensity_completed_point_transport_right
import Theorems.Thm_TypeDensity_concrete_strict_transform_transverse_finite
import Theorems.Thm_TypeDensity_strict_transform_common_point_transport
import Theorems.Thm_TypeDensity_chartBase_apply_eq_algebraMap
import Theorems.Thm_TypeDensity_span_pow_mul_colon_eq
import Theorems.Thm_TypeDensity_concrete_left_point_exceptional_regular
import Theorems.Thm_TypeDensity_concrete_infinity_point_completion
import Theorems.Thm_TypeDensity_concrete_infinity_strict_transform_transverse_finite
import Theorems.Thm_TypeDensity_concrete_surface_parameterIdeal_isMaximal
import Theorems.Thm_TypeDensity_blowupChart_concrete_isNoetherianRing
import Theorems.Thm_TypeDensity_concrete_surface_regular_pair_tx
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

theorem TypeDensity.curve_datum_of_parent_function (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (pi : O) (hpi : Irreducible pi) (u : (TwoSeries O)ˣ)
    (a b : ℕ) (ha : 0 < a) (d : ℕ) (f : ConcreteSurface O pi u a b)
    (c : Fin (d + 1) → ConcreteSurface O pi u a b)
    (hc : f = ∑ i : Fin (d + 1),
      c i * (surfaceT O pi u a b) ^ (d - i.val) * (surfaceX O pi u a b) ^ i.val)
    (hne : ∃ i : Fin (d + 1), c i ∉ Ideal.span {(surfaceT O pi u a b), (surfaceX O pi u a b)})
    (beta : BlowupRestriction (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b)) :
    ∃ D : TwoChartCurveData (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
      (surfaceX O pi u a b) beta,
      (∀ s : D.ι ⊕ D.ι0,
        leftData D s = completedPointMap
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (leftPoint D s)
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b))^i.val) ∧
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b))^i.val) ∈ leftPoint D s) ∧
      (∀ P : Ideal
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)),
        P.IsMaximal →
        (chartBase (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (surfaceT O pi u a b) ∈ P →
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceT O pi u a b)
        (surfaceX O pi u a b))^i.val) ∈ P → ∃ s : D.ι ⊕ D.ι0, leftPoint D s = P) ∧
      (∀ s : D.ι ⊕ D.ιinf,
        Ideal.span {rightData D s} = Ideal.span
        {completedPointMap
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
        (rightPoint D s)
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
        (surfaceT O pi u a b))^(d - i.val))} ∧
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
        (surfaceT O pi u a b))^(d - i.val)) ∈ rightPoint D s) ∧
      (∀ P : Ideal
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)),
        P.IsMaximal →
        (chartBase (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
        (surfaceX O pi u a b) ∈ P →
        (∑ i : Fin (d+1),
        algebraMap (ConcreteSurface O pi u a b)
        (BlowupChart (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b))
        (c i) * (chartSlope (ConcreteSurface O pi u a b) (surfaceX O pi u a b)
        (surfaceT O pi u a b))^(d - i.val)) ∈ P → ∃ s : D.ι ⊕ D.ιinf, rightPoint D s = P) ∧
      (∀ s : D.ι ⊕ D.ι0,
        strictTransformAt (ConcreteSurface O pi u a b) (surfaceT O pi u a b) (surfaceX O pi u a b)
        (leftPoint D s) d (Ideal.span {f}) = Ideal.span {leftData D s}) ∧ ∀ s : D.ι ⊕ D.ιinf,
      strictTransformAt (ConcreteSurface O pi u a b) (surfaceX O pi u a b) (surfaceT O pi u a b)
      (rightPoint D s) d (Ideal.span {f}) = Ideal.span {rightData D s} := by sorry
