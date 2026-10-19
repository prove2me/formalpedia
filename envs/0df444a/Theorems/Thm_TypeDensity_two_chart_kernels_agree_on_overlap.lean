-- Prove2me | Theorems.Thm_TypeDensity_two_chart_kernels_agree_on_overlap
-- name    : TypeDensity.two_chart_kernels_agree_on_overlap
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:53:53.727817+00:00
-- url     : https://prove2.me/theorems/12f70ce2-56f5-4679-9ca8-d4063e319b96
-- title:
--   The level-`j` kernels of the two charts both extend to the common level-`j` kernel on the overlap.
-- statement:
--   The level-`j` kernels of the two charts both extend to the common level-`j` kernel on the overlap.
-- source:
--   TypeDensity/Blowup/TwoChartCurveData.lean#L125-L149

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
import Theorems.Thm_TypeDensity_completed_point_power_contraction
import Theorems.Thm_TypeDensity_two_chart_left_data_transverse_finite
import Theorems.Thm_TypeDensity_two_chart_left_points_maximal
import Theorems.Thm_TypeDensity_two_chart_right_data_transverse_finite
import Theorems.Thm_TypeDensity_finite_support_kernel_localize
import Theorems.Thm_TypeDensity_blowup_overlap_isLocalization_right
import Theorems.Thm_TypeDensity_overlap_exceptional_point_comap_maximal_right
import Theorems.Thm_TypeDensity_rightLevelIdeal_map_rightIso_symm
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

theorem TypeDensity.two_chart_kernels_agree_on_overlap (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (j : ℕ) :
    (leftKernel D j).map (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) = commonKernel D j ∧
      (rightKernel D j).map beta.right.toRingHom = commonKernel D j := by sorry
