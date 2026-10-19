-- Prove2me | Theorems.Thm_TypeDensity_scalar_class_card
-- name    : TypeDensity.scalar_class_card
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:03.877752+00:00
-- url     : https://prove2.me/theorems/992dcf4e-8082-4fc9-800d-a64cab056885
-- title:
--   The nonzero scalar multiples of a nonzero vector over a finite field `k` form a finite set of `|k| − 1` nonzero vectors.
-- statement:
--   The nonzero scalar multiples of a nonzero vector over a finite field `k` form a finite set of `|k| − 1` nonzero vectors.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L1226-L1249

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
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
open scoped ENNReal

theorem TypeDensity.scalar_class_card (k : Type) [Field k] [Finite k] (n : ℕ) (v : Fin (n + 1) → k)
    (hv : v ≠ 0) :
    Nat.card (scalarClass v) = Nat.card k - 1 ∧ (∀ w ∈ scalarClass v, w ≠ 0) ∧
      (scalarClass v).Finite := by sorry
