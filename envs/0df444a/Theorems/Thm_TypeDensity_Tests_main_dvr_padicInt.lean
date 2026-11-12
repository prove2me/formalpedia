-- Prove2me | Theorems.Thm_TypeDensity_Tests_main_dvr_padicInt
-- name    : TypeDensity.Tests.main_dvr_padicInt
-- status  : Proved
-- author  : @asving
-- created : 2026-11-11T19:51:52.659836+00:00
-- url     : https://prove2.me/theorems/bf0a8f26-8b74-4e6b-b8c6-8b90dec6dc4a
-- title:
--   `main_dvr` over `ℤ_[p]`: with Mathlib's topology, the Borel σ-algebra and normalized Haar measure, the type densities over `ℤ_[p]` are the universal expressions evaluated at `q = p`.
-- statement:
--   **`main_dvr` over `ℤ_[p]`.** With Mathlib's topology on the `p`-adic integers, its Borel σ-algebra and normalized Haar measure, the type densities of monic polynomials and of primitive binary forms over `ℤ_[p]` are the universal expressions evaluated at `q = p`.
-- source:
--   Tests/PadicInt.lean#L83-L90

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Cluster_Defs
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
import Definitions.Def_TypeDensity_Tests_PadicInt
import Theorems.Thm_TypeDensity_Tests_isAdic_maximalIdeal_padicInt
import Theorems.Thm_TypeDensity_Tests_card_residueField_padicInt
import Theorems.Thm_TypeDensity_main_dvr
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
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.Basic
set_option autoImplicit false

open TypeDensity TypeDensity.Tests
open IsLocalRing Topology
variable (p : ℕ) [hp : Fact p.Prime]
attribute [local instance] TypeDensity.Tests.padicIntMeasurableSpace TypeDensity.Tests.padicIntBorelSpace

theorem TypeDensity.Tests.main_dvr_padicInt (n : ℕ) (σ : FactorType) :
    monicDensity ℤ_[p] n σ = densityValue (monicExpr n σ) p ∧
      projectiveDensity ℤ_[p] n σ = densityValue (projectiveExpr n σ) p := by sorry
