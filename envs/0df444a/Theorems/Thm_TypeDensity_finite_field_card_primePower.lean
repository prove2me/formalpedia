-- Prove2me | Theorems.Thm_TypeDensity_finite_field_card_primePower
-- name    : TypeDensity.finite_field_card_primePower
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:09.511334+00:00
-- url     : https://prove2.me/theorems/1ea97e50-b869-4836-9441-98f938e8b2cd
-- title:
--   The cardinality of a finite field is a prime power.
-- statement:
--   The cardinality of a finite field is a prime power.
-- source:
--   TypeDensity/Formula/FiniteFieldCounts.lean#L37-L42

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Surfaces_Lengths
import Definitions.Def_TypeDensity_Surfaces_PowerSeries
import Definitions.Def_TypeDensity_Formula_FiniteFieldCounts
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.finite_field_card_primePower (K : Type) [Field K] [Finite K] :
    PrimePower (Nat.card K) := by sorry
