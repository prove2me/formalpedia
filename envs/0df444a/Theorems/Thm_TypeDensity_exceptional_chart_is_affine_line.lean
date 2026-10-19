-- Prove2me | Theorems.Thm_TypeDensity_exceptional_chart_is_affine_line
-- name    : TypeDensity.exceptional_chart_is_affine_line
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:20.283182+00:00
-- url     : https://prove2.me/theorems/15a42b9a-258f-4d8a-8e7e-6ea9e5ccdd34
-- title:
--   The first level `A/(t)` of the `t`-chart is the polynomial ring `(R/(t, x))[Z]`.
-- statement:
--   The first level `A/(t)` of the `t`-chart is the polynomial ring `(R/(t, x))[Z]`.
-- source:
--   TypeDensity/Blowup/CurveOrders.lean#L381-L433

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
import Theorems.Thm_TypeDensity_blowup_chart_relation
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.exceptional_chart_is_affine_line (R : Type) [CommRing R] (t x : R) :
    ∃ e : ExceptionalChartLevel R t x 1 ≃+* Polynomial (R ⧸ Ideal.span {t,x}),
        (∀ r : R, e (levelBase R t x 1 r) = Polynomial.C (Ideal.Quotient.mk (Ideal.span {t,x}) r)) ∧
        e (levelSlope R t x 1) = Polynomial.X := by sorry
