-- Prove2me | Theorems.Thm_TypeDensity_concrete_member_curve_order_free
-- name    : TypeDensity.concrete_member_curve_order_free
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:38:32.410608+00:00
-- url     : https://prove2.me/theorems/a5c3250d-5975-4baa-8771-668ce9fc6f12
-- title:
--   The curve order `R/J` of an ideal `J` in the state set of a concrete member is a free `O`-module of rank the degree of the state.
-- statement:
--   The curve order `R/J` of an ideal `J` in the state set of a concrete member is a free `O`-module of rank the degree of the state.
-- source:
--   TypeDensity/Recursion/Members.lean#L1188-L1217

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
import Theorems.Thm_TypeDensity_concrete_surface_special_fiber_length_transport
import Theorems.Thm_TypeDensity_special_fiber_crossing_contact_regular
import Theorems.Thm_TypeDensity_concrete_surface_single_curve_free
import Theorems.Thm_TypeDensity_concrete_surface_residue_regular_of_special_fiber
import Theorems.Thm_TypeDensity_concrete_surface_contact_eq_special_fiber_contact
import Theorems.Thm_TypeDensity_concrete_surface_special_fiber_equiv
import Theorems.Thm_TypeDensity_concrete_surface_curve_free_of_length
import Theorems.Thm_TypeDensity_crossing_special_fiber_length
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

theorem TypeDensity.concrete_member_curve_order_free (m : ConcreteMember) (J : Ideal m.R)
    (hJ : J ∈ m.toMeasured.stateSet) :
    Module.Free m.O (m.R ⧸ J) ∧ Module.Finite m.O (m.R ⧸ J) ∧ Module.finrank m.O (m.R ⧸ J) =
      m.s.degree := by sorry
