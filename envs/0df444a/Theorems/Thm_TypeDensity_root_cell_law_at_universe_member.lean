-- Prove2me | Theorems.Thm_TypeDensity_root_cell_law_at_universe_member
-- name    : TypeDensity.root_cell_law_at_universe_member
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:45:35.853514+00:00
-- url     : https://prove2.me/theorems/841b83ef-dd52-454d-bf4c-f66ca15f073a
-- title:
--   **Root cell law at a universe member.** Let `i` be a member of a surface universe satisfying the termination hypotheses, whose state is the single state `(1, r)` and whose measure is the pushforward o
-- statement:
--   **Root cell law at a universe member.** Let `i` be a member of a surface universe satisfying the termination hypotheses, whose state is the single state `(1, r)` and whose measure is the pushforward of the coefficient measure along a coordinate chart `z ↦ (f, b)(π z)` matching algebra types with polynomial types. Then the type-`σ` event of `π`-scaled monic polynomials is measurable and has mass `densityValue (lawCoeff (stateLaw (single 1 r)) σ) q`.
-- source:
--   TypeDensity/Recursion/RootCellLaw.lean#L165-L211

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
import Theorems.Thm_TypeDensity_universal_law_statement
import Theorems.Thm_TypeDensity_type_event_null_difference
import Theorems.Thm_TypeDensity_etale_type_event_measurable
import Theorems.Thm_TypeDensity_chart_cell_law_generic
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
open scoped BigOperators ENNReal

theorem TypeDensity.root_cell_law_at_universe_member (U : SurfaceUniverse)
    (hE1 : U.ChildTypesExist)
    (hE2 : U.InvariantDecreases fun i J ↦ (orderDefect (U.M i).O ((U.M i).R ⧸ J)).toNat)
    (i : U.ι) (r : ℕ) (hr : 0 < r)
    (hs : (U.M i).s = State.single 1 r) (f : (U.M i).R)
    (b : Fin (State.single 1 r).degree → (U.M i).R)
    (hmeas : Measurable (coordinateIdeal (U.M i).S.pi f b))
    (hμ : (U.M i).μ = (((U.M i).q : ℝ≥0∞)⁻¹ ^ (State.single 1 r).degree) •
    (coefficientMeasure (U.M i).O (State.single 1 r).degree).map
    (coordinateIdeal (U.M i).S.pi f b)) (hcell : ∀ z : Fin (State.single 1 r).degree → (U.M i).O,
    (coordinateIdeal (U.M i).S.pi f b) z ∈ (U.M i).stateSet)
    (htype : ∀ (z : Fin (State.single 1 r).degree → (U.M i).O) (σ : FactorType), HasAlgebraType
    (U.M i).O ((U.M i).R ⧸ (coordinateIdeal (U.M i).S.pi f b) z) σ ↔ HasPolynomialTypeF (U.M i).O
    (monicPolynomial (U.M i).O ((U.M i).S.pi • z)) σ) (σ : FactorType) :
    MeasurableSet {z : Fin (State.single 1 r).degree → (U.M i).O | HasPolynomialTypeF (U.M i).O
        (monicPolynomial (U.M i).O ((U.M i).S.pi • z)) σ} ∧ coefficientMeasure (U.M i).O
        (State.single 1 r).degree {z : Fin (State.single 1 r).degree → (U.M i).O |
        HasPolynomialTypeF (U.M i).O (monicPolynomial (U.M i).O ((U.M i).S.pi • z)) σ} =
        densityValue (lawCoeff (stateLaw (State.single 1 r)) σ) (U.M i).q := by sorry
