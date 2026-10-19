-- Prove2me | Theorems.Thm_TypeDensity_block_descent_congruence_iff
-- name    : TypeDensity.block_descent_congruence_iff
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:14:53.245272+00:00
-- url     : https://prove2.me/theorems/c6a74047-24f2-422c-990e-b85a6bc1e089
-- title:
--   Frobenius descent preserves congruences: `a ≡ a' (mod 𝔪 ^ L)` coordinatewise if and only if the selected blocks are congruent modulo `(𝔪 O[X]/(Φ)) ^ L`.
-- statement:
--   Frobenius descent preserves congruences: `a ≡ a' (mod 𝔪 ^ L)` coordinatewise if and only if the selected blocks are congruent modulo `(𝔪 O[X]/(Φ)) ^ L`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L1127-L1187

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_base_ideal_pure
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_polynomial_congruence_and_product
import Theorems.Thm_TypeDensity_unramified_is_dvr
import Theorems.Thm_TypeDensity_block_conjugates
import Theorems.Thm_TypeDensity_selectBlock_spec
import Theorems.Thm_TypeDensity_hensel_family_unique_mod_pow
import Theorems.Thm_TypeDensity_monic_coeff_sub_mem_iff
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

theorem TypeDensity.block_descent_congruence_iff (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (r : ℕ) (L : ℕ) (a a' : Fin (Φ.natDegree * r) → O)
    (ha : a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r))
    (ha' : a' ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r)) :
    (∀ j, a j - a' j ∈ (IsLocalRing.maximalIdeal O) ^ L) ↔
      ∀ j, selectBlock O Φ r a j - selectBlock O Φ r a' j ∈ (baseIdeal O Φ) ^ L := by sorry
