-- Prove2me | Theorems.Thm_TypeDensity_Tests_single_four_law_at_two
-- name    : TypeDensity.Tests.single_four_law_at_two
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:32.144553+00:00
-- url     : https://prove2.me/theorems/6c148a09-5686-4cc2-8b56-0d7642650e23
-- title:
--   single four law at two
-- statement:
--   At `q = 2`, the law of the single state `S(1;4)` has the eleven explicit rational coefficients listed in the statement on the eleven quartic factorization types (e.g. `856/1533` on `{(4,1)}`), and coefficient `0` on every other type.
-- source:
--   Tests/Regression.lean#L1754-L1807

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
import Theorems.Thm_TypeDensity_Tests_coeff_mul_of_mem
import Theorems.Thm_TypeDensity_Tests_shiftedCoeff_prod_perm
import Theorems.Thm_TypeDensity_Tests_flatMap_replicate_eq
import Theorems.Thm_TypeDensity_Tests_divisorCount_spat
import Theorems.Thm_TypeDensity_Tests_pattern_eq_of_weight_two
import Theorems.Thm_TypeDensity_Tests_children_valid
import Theorems.Thm_TypeDensity_Tests_nonself_child_rank_lt
import Theorems.Thm_TypeDensity_Tests_stateLawFuel_eq
import Theorems.Thm_TypeDensity_Tests_crossing_one_one_law
import Theorems.Thm_TypeDensity_Tests_crossing_left_one_law
import Theorems.Thm_TypeDensity_Tests_crossing_right_one_law
import Theorems.Thm_TypeDensity_Tests_single_two_law
import Theorems.Thm_TypeDensity_Tests_single_three_law
import Theorems.Thm_TypeDensity_Tests_allowed_single_one_four_iff
import Theorems.Thm_TypeDensity_Tests_coeff_m4QuadraticContact
import Theorems.Thm_TypeDensity_Tests_coeff_m4TwoTangent
import Theorems.Thm_TypeDensity_Tests_divisorCount_m4_at_two
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

theorem TypeDensity.Tests.single_four_law_at_two (σ : FactorType) :
    (Expr.eval 2 (lawCoeff (stateLaw (.single 1 4)) σ)) = (if σ = {(4,1)} then 856/1533 else 0) +
      (if σ = {(2,2)} then 566/7665 else 0) + (if σ = {(1,4)} then 31/10220 else 0) +
      (if σ = {(2,1),(2,1)} then 2/63 else 0) + (if σ = {(1,2),(1,2)} then 83/183960 else 0) +
      (if σ = {(1,2),(2,1)} then 103/4599 else 0) +
      (if σ = {(1,1),(3,1)} then 4484/15841 else 0) + (if σ = {(1,1),(1,3)} then 9/2263 else 0) +
      (if σ = {(1,1),(1,1),(2,1)} then 3085/142569 else 0) +
      (if σ = {(1,1),(1,1),(1,2)} then 817/570276 else 0) +
      (if σ = {(1,1),(1,1),(1,1),(1,1)} then 43/1140552 else 0) := by sorry
