-- Prove2me | Theorems.Thm_TypeDensity_global_function_of_two_chart_curve_data
-- name    : TypeDensity.global_function_of_two_chart_curve_data
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:25:39.614322+00:00
-- url     : https://prove2.me/theorems/9e63e47c-d9e4-4aa1-a6bf-640d6867b8bf
-- title:
--   Two-chart curve data with normalized level generators come from a global function `f` and glued generators.
-- statement:
--   Two-chart curve data with normalized level generators come from a global function `f` and glued generators.
-- source:
--   TypeDensity/Recursion/Termination.lean#L439-L460

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
import Definitions.Def_TypeDensity_Surfaces_ConcreteAtlas
import Definitions.Def_TypeDensity_Recursion_Members
import Definitions.Def_TypeDensity_Measure_MemberCharts
import Definitions.Def_TypeDensity_Recursion_Termination
import Theorems.Thm_TypeDensity_glued_function_exists_unique
import Theorems.Thm_TypeDensity_glued_generators_of_two_chart_curve_data
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
open IsLocalRing MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.global_function_of_two_chart_curve_data (R : Type) [CommRing R] (t x : R)
    (beta : BlowupRestriction R t x) (D : TwoChartCurveData R t x beta)
    [(Ideal.span ({t,x} : Set R)).IsMaximal] [IsLocalRing R] [IsNoetherianRing (BlowupChart R t x)]
    [IsNoetherianRing (BlowupChart R x t)] [IsAdicComplete (Ideal.span {t,x}) R]
    (hreg : RegularParameterPair R t x) (hregSwap : RegularParameterPair R x t) (d : ℕ)
    (FA : ℕ → BlowupChart R t x) (hFA : ∀ j : ℕ, leftLevelKernel D j = Ideal.span
    {Ideal.Quotient.mk ((Ideal.span {chartBase R t x t})^j) (FA j)}) (FB : ℕ → BlowupChart R x t)
    (hFB : ∀ j : ℕ, rightLevelKernel D j = Ideal.span {Ideal.Quotient.mk
    ((Ideal.span {chartBase R x t x})^j) (FB j)}) (hnorm : ∃ u : Rˣ,
    (algebraMap (BlowupChart R t x) (BlowupOverlap R t x)) (FA 1) - algebraMap R
    (BlowupOverlap R t x) (u : R) * ((overlapSlope R t x)^d * beta.right (FB 1)) ∈
    (Ideal.span {overlapException R t x})) :
    ∃ f : R, ∃ G : GluedGenerators R t x beta d, (∀ j : ℕ, surfaceToCechInput R t x j f =
      (cechInputLattice R t x j).mkQ (gluedFunctionPair R t x G j)) ∧ ∀ j : ℕ, Ideal.span
      {Ideal.Quotient.mk ((chartExceptional R t x)^j) (G.left j)} = leftLevelKernel D j ∧ Ideal.span
      {Ideal.Quotient.mk ((chartExceptional R x t)^j) (G.right j)} = rightLevelKernel D j := by sorry
