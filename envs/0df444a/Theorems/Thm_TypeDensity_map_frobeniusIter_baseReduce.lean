-- Prove2me | Theorems.Thm_TypeDensity_map_frobeniusIter_baseReduce
-- name    : TypeDensity.map_frobeniusIter_baseReduce
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:52:57.845791+00:00
-- url     : https://prove2.me/theorems/67e5c0aa-9434-452f-9390-07987a8670b4
-- title:
--   Applying the `i`-th Frobenius iterate to a polynomial reducing to `(X - θ̄) ^ r` gives a polynomial reducing to `(X - θ̄ ^ (q ^ i)) ^ r`.
-- statement:
--   Applying the `i`-th Frobenius iterate to a polynomial reducing to `(X - θ̄) ^ r` gives a polynomial reducing to `(X - θ̄ ^ (q ^ i)) ^ r`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L866-L888

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_frobenius_residue_action
import Theorems.Thm_TypeDensity_conjugate_roots_distinct
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

theorem TypeDensity.map_frobeniusIter_baseReduce (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r i : ℕ) (B : Polynomial (AdjoinRoot Φ))
    (hB : B.map (baseReduce O Φ) = conjugateFactor O Φ 0 ^ r) :
    (B.map (frobeniusIter O Φ i).toRingHom).map (baseReduce O Φ) = conjugateFactor O Φ i ^ r := by sorry
