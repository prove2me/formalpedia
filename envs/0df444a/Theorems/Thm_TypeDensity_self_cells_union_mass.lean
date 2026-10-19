-- Prove2me | Theorems.Thm_TypeDensity_self_cells_union_mass
-- name    : TypeDensity.self_cells_union_mass
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:21.707544+00:00
-- url     : https://prove2.me/theorems/2c634e9b-077e-4343-8cff-4a3a072a280c
-- title:
--   One more return at `single a c`: if an event family `E` is measurable with mass `m · vol` at every member in state `single a c` with the same residue cardinality, then the union over the self cells of
-- statement:
--   One more return at `single a c`: if an event family `E` is measurable with mass `m · vol` at every member in state `single a c` with the same residue cardinality, then the union over the self cells of `i` of the child boxes of `E` is measurable with mass `λ · m · vol`, where `λ` is the return weight.
-- source:
--   TypeDensity/Recursion/Events.lean#L343-L390

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
import Definitions.Def_TypeDensity_Recursion_ChildMembers
import Theorems.Thm_TypeDensity_density_value_arith
import Theorems.Thm_TypeDensity_self_patterns_of_single_state
import Theorems.Thm_TypeDensity_universe_basic_facts
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal TensorProduct

theorem TypeDensity.self_cells_union_mass (U : SurfaceUniverse) {a c : ℕ} (ha : 0 < a) (hc : 2 ≤ c)
    (i : U.ι) (hs : (U.M i).s = State.single a c) (E : ∀ i' : U.ι, Set (Ideal (U.M i').R))
    (m : ℝ≥0∞)
    (hE : ∀ i' : U.ι, (U.M i').s = State.single a c → (U.M i').q = (U.M i).q →
      (U.M i').μ (E i') = m * (U.M i').μ (U.M i').stateSet ∧ MeasurableSet (E i')) :
    (U.M i).μ (⋃ c' : U.selfCells i, U.childBox i c'.1 (fun j ↦ E (U.child i c'.1 j))) =
      densityValue (returnWeight c) (U.M i).q * m * (U.M i).μ (U.M i).stateSet ∧
    MeasurableSet (⋃ c' : U.selfCells i, U.childBox i c'.1 (fun j ↦ E (U.child i c'.1 j))) := by sorry
