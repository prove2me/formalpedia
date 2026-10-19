-- Prove2me | Theorems.Thm_TypeDensity_concrete_member_state_generator_regular
-- name    : TypeDensity.concrete_member_state_generator_regular
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:32.243728+00:00
-- url     : https://prove2.me/theorems/5deb9665-a71b-4b2b-a808-8ffa09fbaeb1
-- title:
--   A generator of an ideal of the state set is a nonzero nonunit that is regular modulo `π`.
-- statement:
--   A generator of an ideal of the state set is a nonzero nonunit that is regular modulo `π`.
-- source:
--   TypeDensity/Recursion/Members.lean#L962-L997

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
import Theorems.Thm_TypeDensity_surface_state_ideal_proper
import Theorems.Thm_TypeDensity_surface_vertical_parameter
import Theorems.Thm_TypeDensity_principal_ideal_image
import Theorems.Thm_TypeDensity_regular_principal_generators_associated
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
open IsLocalRing MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.concrete_member_state_generator_regular (m : ConcreteMember) (g : m.toMeasured.R)
    (hg : Ideal.span {g} ∈ m.toMeasured.stateSet) :
    g ≠ 0 ∧ ¬ IsUnit g ∧ Function.Injective (fun y : m.toMeasured.R ⧸ Ideal.span
      {(algebraMap m.toMeasured.O m.toMeasured.R m.toMeasured.S.pi)} => y * Ideal.Quotient.mk
      (Ideal.span {(algebraMap m.toMeasured.O m.toMeasured.R m.toMeasured.S.pi)}) g) := by sorry
