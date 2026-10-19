-- Prove2me | Theorems.Thm_TypeDensity_two_chart_right_data_transverse_finite
-- name    : TypeDensity.two_chart_right_data_transverse_finite
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:27.960983+00:00
-- url     : https://prove2.me/theorems/8c241df7-b0d0-49b3-8e4b-d7e3502a9100
-- title:
--   At every point of the second chart in two-chart curve data, the exceptional parameter is a nonzerodivisor modulo the local equation, and some power of the maximal ideal of the completion lies in the l
-- statement:
--   At every point of the second chart in two-chart curve data, the exceptional parameter is a nonzerodivisor modulo the local equation, and some power of the maximal ideal of the completion lies in the level-`j` local curve ideal.
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L1083-L1108

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
import Theorems.Thm_TypeDensity_beta_right_chartBase_self
import Theorems.Thm_TypeDensity_mul_injective_quotient_transport
import Theorems.Thm_TypeDensity_sup_pow_le
import Theorems.Thm_TypeDensity_exists_pow_le_span_pair_transport
import Theorems.Thm_TypeDensity_map_maximalIdeal_localCompletion_comap_le
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

theorem TypeDensity.two_chart_right_data_transverse_finite (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta) (j : ℕ) :
    (∀ s, Function.Injective (fun a : CompletedLocalAt (BlowupChart R x t) (rightPoint D s) ⧸
      Ideal.span {rightData D s} => Ideal.Quotient.mk (Ideal.span {rightData D s})
      (completedPointMap (BlowupChart R x t) (rightPoint D s) (chartBase R x t x)) * a)) ∧ ∀ s, ∃ L
      : ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime (rightPoint D s))).map
      (localCompletionMap (Localization.AtPrime (rightPoint D s))))^L ≤ rightLevelIdeal D j s := by sorry
