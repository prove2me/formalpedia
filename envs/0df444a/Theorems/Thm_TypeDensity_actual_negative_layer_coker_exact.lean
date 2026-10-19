-- Prove2me | Theorems.Thm_TypeDensity_actual_negative_layer_coker_exact
-- name    : TypeDensity.actual_negative_layer_coker_exact
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:53:01.25073+00:00
-- url     : https://prove2.me/theorems/50ffb43c-e130-45b2-bf92-f332571abf35
-- title:
--   In the negative range `j < d`, the reduction map between the cokernels at levels `j + 1` and `j` has kernel the image of an injection from `(R ⧸ (t, x))^(d - j - 1)`.
-- statement:
--   In the negative range `j < d`, the reduction map between the cokernels at levels `j + 1` and `j` has kernel the image of an injection from `(R ⧸ (t, x))^(d - j - 1)`.
-- source:
--   TypeDensity/Blowup/TwoChartCurveData.lean#L1317-L1376

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
import Theorems.Thm_TypeDensity_blowup_chart_relation
import Theorems.Thm_TypeDensity_overlap_layer_laurent_coordinates
import Theorems.Thm_TypeDensity_actual_negative_twist_kernel_zero
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

theorem TypeDensity.actual_negative_layer_coker_exact (R : Type) [CommRing R] (t x : R) (hreg :
    RegularParameterPair R t x) (beta : BlowupRestriction R t x) (hregSwap : RegularParameterPair R
    x t) (d j : ℕ) (hj : j < d) (hnext : cechInputLattice R t x (j + 1) ≤
    (cechOutputLattice R t x (j + 1)).comap (fullCechDifferential R t x beta d)) (hnow :
    cechInputLattice R t x j ≤
    (cechOutputLattice R t x j).comap (fullCechDifferential R t x beta d)) (hcomm :
    (cechOutputReduction R t x j).comp (finiteCechDifferential R t x beta d (j + 1) hnext) =
    (finiteCechDifferential R t x beta d j hnow).comp (cechInputReduction R t x j)) :
    ∃ i : (Fin (d-j-1) → (R ⧸ Ideal.span {t,x})) →ₗ[R] (CechLevelOutput R t x (j+1) ⧸
      LinearMap.range (finiteCechDifferential R t x beta d (j+1) hnext)), Function.Injective i ∧
      Function.Exact i (twoTermCokerMap (finiteCechDifferential R t x beta d (j+1) hnext)
      (finiteCechDifferential R t x beta d j hnow) (cechInputReduction R t x j)
      (cechOutputReduction R t x j) hcomm) := by sorry
