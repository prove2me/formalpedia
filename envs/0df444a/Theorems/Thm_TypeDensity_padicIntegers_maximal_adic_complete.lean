-- Prove2me | Theorems.Thm_TypeDensity_padicIntegers_maximal_adic_complete
-- name    : TypeDensity.padicIntegers_maximal_adic_complete
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:20:06.011694+00:00
-- url     : https://prove2.me/theorems/098d3477-c937-45d6-9ab6-a5bc93606c86
-- title:
--   The ring of integers of a finite extension of `ℚ_[p]` is complete for its maximal ideal.
-- statement:
--   The ring of integers of a finite extension of `ℚ_[p]` is complete for its maximal ideal.
-- source:
--   TypeDensity/Measure/PrimitiveLocus.lean#L337-L348

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Theorems.Thm_TypeDensity_integral_closure_own_adic_complete
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
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.padicIntegers_maximal_adic_complete (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (hdvr : IsDiscreteValuationRing (padicIntegers p K)) :
    letI := hdvr
    IsAdicComplete (IsLocalRing.maximalIdeal (padicIntegers p K)) (padicIntegers p K) := by sorry
