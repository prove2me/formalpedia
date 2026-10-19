-- Prove2me | Theorems.Thm_TypeDensity_Tests_allowed_single_one_four_iff
-- name    : TypeDensity.Tests.allowed_single_one_four_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:23.594327+00:00
-- url     : https://prove2.me/theorems/d4ced6d7-9331-4106-b3d3-bf5c629e402c
-- title:
--   allowed single one four iff
-- statement:
--   A tangent pattern `(d, rt, rx, m)` of degree `4` is allowed for the single state `S(1;4)` if and only if it is one of the nineteen explicitly listed patterns (eight with `d ≤ 3` and the eleven quartic patterns with `d = 4`).
-- source:
--   Tests/Regression.lean#L1513-L1569

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

theorem TypeDensity.Tests.allowed_single_one_four_iff (d rt rx : Fin 5) (m : Pattern 4) :
    Allowed (State.single 1 4) (⟨d, rt, rx, m⟩ : TangentPattern 4) ↔
      (⟨d, rt, rx, m⟩ : TangentPattern 4) ∈ ({⟨1, 1, 0, fun _ ↦ 0⟩, ⟨2, 2, 0, fun _ ↦ 0⟩,
    ⟨2, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩, ⟨3, 3, 0, fun _ ↦ 0⟩,
    ⟨3, 2, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 1 else 0⟩,
    ⟨3, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 0 then 2 else 0⟩,
    ⟨3, 1, 0, fun ij ↦ if ij.1.val = 0 ∧ ij.2.val = 1 then 1 else 0⟩,
    ⟨3, 1, 0, fun ij ↦ if ij.1.val = 1 ∧ ij.2.val = 0 then 1 else 0⟩,
    ⟨4, 0, 0, m4Split⟩, ⟨4, 0, 0, m4SplitTangent⟩, ⟨4, 0, 0, m4SplitQuadratic⟩,
    ⟨4, 0, 0, m4ContactThree⟩, ⟨4, 0, 0, m4Cubic⟩, ⟨4, 0, 0, m4TwoTangent⟩,
    ⟨4, 0, 0, m4TangentQuadratic⟩, ⟨4, 0, 0, m4TwoQuadratic⟩, ⟨4, 0, 0, m4QuadraticContact⟩,
    ⟨4, 0, 0, m4Inert⟩, ⟨4, 0, 0, m4Contact⟩} : Finset (TangentPattern 4)) := by sorry
