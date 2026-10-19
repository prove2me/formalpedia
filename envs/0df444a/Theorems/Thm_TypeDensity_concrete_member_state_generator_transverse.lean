-- Prove2me | Theorems.Thm_TypeDensity_concrete_member_state_generator_transverse
-- name    : TypeDensity.concrete_member_state_generator_transverse
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:32:12.99742+00:00
-- url     : https://prove2.me/theorems/c78a5f34-f035-49e7-8404-d9966e15235d
-- title:
--   A generator `g` of an ideal of the state set and the parameter `T` form a regular sequence in both orders.
-- statement:
--   A generator `g` of an ideal of the state set and the parameter `T` form a regular sequence in both orders.
-- source:
--   TypeDensity/Recursion/Members.lean#L1078-L1137

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
import Theorems.Thm_TypeDensity_ideal_contact_generator
import Theorems.Thm_TypeDensity_concrete_surface_quotient_T_equiv
import Theorems.Thm_TypeDensity_concrete_surface_equiv_curve_length_and_regular
import Theorems.Thm_TypeDensity_concrete_surface_equiv_regular_pair
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

theorem TypeDensity.concrete_member_state_generator_transverse (m : ConcreteMember) (g : m.toMeasured.R)
    (hg : Ideal.span {g} ∈ m.toMeasured.stateSet) :
    Function.Injective (fun w : m.toMeasured.R ⧸ Ideal.span {m.toMeasured.S.t} => Ideal.Quotient.mk
      (Ideal.span {m.toMeasured.S.t}) g * w) ∧ Function.Injective
      (fun y : m.toMeasured.R ⧸ Ideal.span {g} => Ideal.Quotient.mk (Ideal.span {g})
      m.toMeasured.S.t * y) := by sorry
