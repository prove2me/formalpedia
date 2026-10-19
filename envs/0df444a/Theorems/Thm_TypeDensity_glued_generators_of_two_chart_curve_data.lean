-- Prove2me | Theorems.Thm_TypeDensity_glued_generators_of_two_chart_curve_data
-- name    : TypeDensity.glued_generators_of_two_chart_curve_data
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:15:43.278212+00:00
-- url     : https://prove2.me/theorems/b4d0bc8d-08b5-40be-9341-656d8c3a2f96
-- title:
--   Two-chart curve data with normalized level generators yield glued generators whose level ideals are the level kernels of the two charts.
-- statement:
--   Two-chart curve data with normalized level generators yield glued generators whose level ideals are the level kernels of the two charts.
-- source:
--   TypeDensity/Blowup/TwoChartCurveData.lean#L674-L712

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
import Theorems.Thm_TypeDensity_finite_support_generators_compatible
import Theorems.Thm_TypeDensity_glued_generators_exist
import Theorems.Thm_TypeDensity_two_chart_left_data_transverse_finite
import Theorems.Thm_TypeDensity_two_chart_left_points_maximal
import Theorems.Thm_TypeDensity_two_chart_right_data_transverse_finite
import Theorems.Thm_TypeDensity_finite_support_level_generator_regular
import Theorems.Thm_TypeDensity_overlap_level_generator_regular
import Theorems.Thm_TypeDensity_two_chart_level_generators_agree_on_overlap
import Theorems.Thm_TypeDensity_two_chart_right_points_maximal
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

theorem TypeDensity.glued_generators_of_two_chart_curve_data (R : Type) [CommRing R] (t x : R) (beta :
    BlowupRestriction R t x) (D : TwoChartCurveData R t x beta)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsLocalRing R] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (hreg : RegularParameterPair R t x) (hregSwap :
    RegularParameterPair R x t) (d : ℕ) (FA : ℕ → BlowupChart R t x) (hFA : ∀ j : ℕ, leftLevelKernel
    D j = Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R t x t})^j) (FA j)}) (FB : ℕ →
    BlowupChart R x t) (hFB : ∀ j : ℕ, rightLevelKernel D j =
    Ideal.span {Ideal.Quotient.mk ((Ideal.span {chartBase R x t x})^j) (FB j)}) (hnorm : ∃ u : Rˣ,
    (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (FA 1) - algebraMap
    R (BlowupOverlap R t x) (u : R) * ((overlapSlope R t x)^d * beta.right (FB 1)) ∈
    (Ideal.span {overlapException R t x})) :
    ∃ G : GluedGenerators R t x beta d, ∀ j : ℕ,
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧
      Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} =
        rightLevelKernel D j := by sorry
