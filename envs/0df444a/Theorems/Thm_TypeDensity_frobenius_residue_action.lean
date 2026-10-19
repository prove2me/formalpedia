-- Prove2me | Theorems.Thm_TypeDensity_frobenius_residue_action
-- name    : TypeDensity.frobenius_residue_action
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:08.228428+00:00
-- url     : https://prove2.me/theorems/95036866-1ef3-478b-b2ed-e9856de5d9b4
-- title:
--   Modulo `𝔪`, the Frobenius acts as `x ↦ x ^ q`, and its `i`-th iterate as `x ↦ x ^ (q ^ i)`.
-- statement:
--   Modulo `𝔪`, the Frobenius acts as `x ↦ x ^ q`, and its `i`-th iterate as `x ↦ x ^ (q ^ i)`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L409-L447

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_eval_at_pow_card
import Theorems.Thm_TypeDensity_unramified_adic_complete
import Theorems.Thm_TypeDensity_simple_root_derivative_unit
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
open scoped BigOperators ENNReal

theorem TypeDensity.frobenius_residue_action (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    (∀ x : AdjoinRoot Φ,
      baseReduce O Φ (unramifiedFrobenius O Φ x) = (baseReduce O Φ x) ^ residueCard O) ∧
    (∀ (i : ℕ) (x : AdjoinRoot Φ),
      baseReduce O Φ (frobeniusIter O Φ i x) = (baseReduce O Φ x) ^ (residueCard O ^ i)) := by sorry
