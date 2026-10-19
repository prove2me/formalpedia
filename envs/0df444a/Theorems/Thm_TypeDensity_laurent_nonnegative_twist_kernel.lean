-- Prove2me | Theorems.Thm_TypeDensity_laurent_nonnegative_twist_kernel
-- name    : TypeDensity.laurent_nonnegative_twist_kernel
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:35.813127+00:00
-- url     : https://prove2.me/theorems/5a56d85f-a2a3-4474-9c74-436a17c3c08c
-- title:
--   If `P(T) = T^m · Q(T⁻¹)` in `k[T, T⁻¹]` with `m ≥ 0`, then `deg P ≤ m` and `Q` is the reversal of `P` at level `m`.
-- statement:
--   If `P(T) = T^m · Q(T⁻¹)` in `k[T, T⁻¹]` with `m ≥ 0`, then `deg P ≤ m` and `Q` is the reversal of `P` at level `m`.
-- source:
--   TypeDensity/Blowup/ExceptionalLayers.lean#L299-L323

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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.laurent_nonnegative_twist_kernel (k : Type) [CommRing k] (m : ℕ) (P Q : Polynomial k)
    (h : P.toLaurent =
      LaurentPolynomial.T (m : ℤ) * LaurentPolynomial.invert (R := k) Q.toLaurent) :
    P.natDegree ≤ m ∧ ∀ i : ℕ, Q.coeff i = if i ≤ m then P.coeff (m - i) else 0 := by sorry
