-- Prove2me | Theorems.Thm_TypeDensity_two_chart_left_data_transverse_finite
-- name    : TypeDensity.two_chart_left_data_transverse_finite
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:29.992982+00:00
-- url     : https://prove2.me/theorems/73318974-9bb6-42b7-8478-6e9c3ee2ef69
-- title:
--   At every point of the first chart in two-chart curve data, the exceptional parameter is a nonzerodivisor modulo the local equation, and some power of the maximal ideal of the completion lies in the le
-- statement:
--   At every point of the first chart in two-chart curve data, the exceptional parameter is a nonzerodivisor modulo the local equation, and some power of the maximal ideal of the completion lies in the level-`j` local curve ideal.
-- source:
--   TypeDensity/Blowup/CurveSections.lean#L995-L1015

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

theorem TypeDensity.two_chart_left_data_transverse_finite (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta) (j : ℕ) :
    (∀ s, Function.Injective (fun a : CompletedLocalAt (BlowupChart R t x) (leftPoint D s) ⧸
      Ideal.span {leftData D s} => Ideal.Quotient.mk (Ideal.span {leftData D s})
      (completedPointMap (BlowupChart R t x) (leftPoint D s) (chartBase R t x t)) * a)) ∧ ∀ s, ∃ L :
      ℕ, ((IsLocalRing.maximalIdeal (Localization.AtPrime (leftPoint D s))).map (localCompletionMap
      (Localization.AtPrime (leftPoint D s))))^L ≤ leftLevelIdeal D j s := by sorry
