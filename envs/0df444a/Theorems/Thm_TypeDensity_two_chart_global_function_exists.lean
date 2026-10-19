-- Prove2me | Theorems.Thm_TypeDensity_two_chart_global_function_exists
-- name    : TypeDensity.two_chart_global_function_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:32:42.496831+00:00
-- url     : https://prove2.me/theorems/1683776b-82ef-4780-a413-7db3d24d7f7c
-- title:
--   A two-chart curve datum on a complete regular local surface comes from a global function `f` whose glued level generators cut out the left and right level kernels.
-- statement:
--   A two-chart curve datum on a complete regular local surface comes from a global function `f` whose glued level generators cut out the left and right level kernels.
-- source:
--   TypeDensity/Blowup/FixedTangentCellBijection.lean#L303-L319

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
import Definitions.Def_TypeDensity_Blowup_DivisorPoints
import Definitions.Def_TypeDensity_Blowup_TwoChartCurveData
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Definitions.Def_TypeDensity_Recursion_Termination
import Theorems.Thm_TypeDensity_exceptional_line_equiv_chart_exceptional
import Theorems.Thm_TypeDensity_two_chart_right_data_transverse_finite
import Theorems.Thm_TypeDensity_two_chart_common_multiplicity_eq
import Theorems.Thm_TypeDensity_level_one_kernel_polynomial
import Theorems.Thm_TypeDensity_two_chart_left_level_one_kernel_polynomial
import Theorems.Thm_TypeDensity_glued_level_one_normalization
import Theorems.Thm_TypeDensity_overlap_level_generator_regular
import Theorems.Thm_TypeDensity_overlap_exceptional_point_comap_maximal_right
import Theorems.Thm_TypeDensity_overlap_point_residue_field_equiv
import Theorems.Thm_TypeDensity_two_chart_level_generators_agree_on_overlap
import Theorems.Thm_TypeDensity_two_chart_right_points_maximal
import Theorems.Thm_TypeDensity_two_chart_level_generators_exist
import Theorems.Thm_TypeDensity_global_function_of_two_chart_curve_data
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
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.two_chart_global_function_exists (R : Type) [CommRing R] (t x : R) (beta : BlowupRestriction
    R t x) (D : TwoChartCurveData R t x beta) [(Ideal.span ({t,x} : Set R)).IsMaximal]
    [IsLocalRing R] [IsNoetherianRing (BlowupChart R t x)] [IsNoetherianRing (BlowupChart R x t)]
    [IsAdicComplete (Ideal.span {t,x}) R] (hreg : RegularParameterPair R t x)
    (hregSwap : RegularParameterPair R x t) :
    ∃ f : R, ∃ G : GluedGenerators R t x beta (curveDataDegree D),
        (∀ j : ℕ, surfaceToCechInput R t x j f = (cechInputLattice R t x j).mkQ (gluedFunctionPair R
        t x G j)) ∧ ∀ j : ℕ, Ideal.span {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)}
        = leftLevelKernel D j ∧
        Ideal.span {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D
        j := by sorry
