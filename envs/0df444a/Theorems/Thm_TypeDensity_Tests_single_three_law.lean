-- Prove2me | Theorems.Thm_TypeDensity_Tests_single_three_law
-- name    : TypeDensity.Tests.single_three_law
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:57.750975+00:00
-- url     : https://prove2.me/theorems/71ff979b-5b1d-42d7-b30e-74338b113851
-- title:
--   single three law
-- statement:
--   For every rational `q > 1`, the law of the single state `S(1;3)` has the explicit coefficients, evaluated at `q`, on the five types `{(3,1)}`, `{(1,3)}`, `{(1,1),(2,1)}`, `{(1,1),(1,2)}`, `{(1,1),(1,1),(1,1)}` given in the statement (rational functions with denominator divisible by `q⁴ + q³ + q² + q + 1`), and coefficient `0` on every other type.
-- source:
--   Tests/Regression.lean#L1333-L1364

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Blowup_Directions
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Formula_PatternCounts
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
import Definitions.Def_TypeDensity_Recursion_OrderDefect
import Definitions.Def_TypeDensity_Assembly_NullBridges
import Definitions.Def_TypeDensity_Assembly_TypeEvents
import Definitions.Def_TypeDensity_Assembly_MonicCells
import Definitions.Def_TypeDensity_Blowup_DivisorPoints
import Definitions.Def_TypeDensity_Measure_MemberBoxes
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Definitions.Def_TypeDensity_Recursion_RootCellLaw
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Definitions.Def_TypeDensity_Tests_NonVacuity
import Definitions.Def_TypeDensity_Tests_Regression
import Theorems.Thm_TypeDensity_Tests_coeff_mul_atom
import Theorems.Thm_TypeDensity_Tests_shiftedCoeff_prod_perm
import Theorems.Thm_TypeDensity_Tests_divisorCount_spat
import Theorems.Thm_TypeDensity_Tests_children_valid
import Theorems.Thm_TypeDensity_Tests_nonself_child_rank_lt
import Theorems.Thm_TypeDensity_Tests_stateLawFuel_eq
import Theorems.Thm_TypeDensity_Tests_crossing_one_one_law
import Theorems.Thm_TypeDensity_Tests_crossing_left_one_law
import Theorems.Thm_TypeDensity_Tests_crossing_right_one_law
import Theorems.Thm_TypeDensity_Tests_single_two_law
import Theorems.Thm_TypeDensity_Tests_allowed_single_one_three_iff
import Theorems.Thm_TypeDensity_Tests_divisorCount_m3
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Separation.Lemmas
set_option autoImplicit false

open TypeDensity TypeDensity.Tests
set_option autoImplicit false
open scoped BigOperators ENNReal

theorem TypeDensity.Tests.single_three_law (q : ℚ) (hq : 1 < q) (σ : FactorType) :
    (Expr.eval q (lawCoeff (stateLaw (.single 1 3)) σ)) =
      (if σ = {(3,1)} then q^2*(q^2+1)/(q^4+q^3+q^2+q+1) else 0) +
      (if σ = {(1,3)} then (q+1)/(3*(q^4+q^3+q^2+q+1)) else 0) +
      (if σ = {(1,1),(2,1)} then q*(q^3+q^2+1)/((q+1)*(q^4+q^3+q^2+q+1)) else 0) +
      (if σ = {(1,1),(1,2)} then (q^2+q+1)/(2*(q+1)*(q^4+q^3+q^2+q+1)) else 0) +
      (if σ = {(1,1),(1,1),(1,1)} then (q^2-q+1)/(6*(q+1)*(q^4+q^3+q^2+q+1)) else 0) := by sorry
