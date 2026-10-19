-- Prove2me | Theorems.Thm_TypeDensity_curve_sections_quot_equiv_product
-- name    : TypeDensity.curve_sections_quot_equiv_product
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:36.565983+00:00
-- url     : https://prove2.me/theorems/41ad7eb6-9cf0-44ad-8b6f-da3c51d31111
-- title:
--   The level-`j` quotient of curve sections is additively isomorphic to the product of the local level quotients at all points, compatibly with `sectionsToProduct`.
-- statement:
--   The level-`j` quotient of curve sections is additively isomorphic to the product of the local level quotients at all points, compatibly with `sectionsToProduct`.
-- source:
--   TypeDensity/Blowup/TwoChartCurveData.lean#L346-L447

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
import Theorems.Thm_TypeDensity_curve_ideal_lattice_eq_kernels
import Theorems.Thm_TypeDensity_finite_support_quotient_surjective_of_isPrime
import Theorems.Thm_TypeDensity_two_chart_left_data_transverse_finite
import Theorems.Thm_TypeDensity_two_chart_left_points_maximal
import Theorems.Thm_TypeDensity_two_chart_right_data_transverse_finite
import Theorems.Thm_TypeDensity_rightLevelIdeal_map_rightIso_symm
import Theorems.Thm_TypeDensity_two_chart_kernels_agree_on_overlap
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

theorem TypeDensity.curve_sections_quot_equiv_product (R : Type) [CommRing R] (t x : R)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] (beta : BlowupRestriction R t x) (D : TwoChartCurveData R
    t x beta) (d : ℕ) (G : GluedGenerators R t x beta d) (hG : ∀ j : ℕ,
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧
    Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D j)
    (j : ℕ) :
    ∃ E : curveSectionsQuot R t x beta G j ≃+ curveProduct D j, ∀ q : curveSectionsQuot R t x beta G
      j, ∀ p : BlowupChart R t x × BlowupChart R x t,
      (q : (BlowupChart R t x × BlowupChart R x t) ⧸ curveIdealLattice R t x beta G j) =
      (curveIdealLattice R t x beta G j).mkQ p → E q = sectionsToProduct D j p := by sorry
