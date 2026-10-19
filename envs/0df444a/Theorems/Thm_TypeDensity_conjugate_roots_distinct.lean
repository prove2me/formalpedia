-- Prove2me | Theorems.Thm_TypeDensity_conjugate_roots_distinct
-- name    : TypeDensity.conjugate_roots_distinct
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:15.814772+00:00
-- url     : https://prove2.me/theorems/7ef178f0-d8f6-4526-9142-c697615df04b
-- title:
--   The residue roots `θ̄^(q^i)`, `i < deg Φ`, are pairwise distinct roots of `Φ̄` in `k_δ`, so `Φ̄` splits there as the product of the pairwise coprime conjugate factors.
-- statement:
--   The residue roots `θ̄^(q^i)`, `i < deg Φ`, are pairwise distinct roots of `Φ̄` in `k_δ`, so `Φ̄` splits there as the product of the pairwise coprime conjugate factors.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L1117-L1196

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_eval_at_pow_card
import Theorems.Thm_TypeDensity_residue_extension_field
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

theorem TypeDensity.conjugate_roots_distinct (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) :
    (∀ c : O, residueEmbed O Φ (IsLocalRing.residue O c) = baseReduce O Φ
        (algebraMap O (AdjoinRoot Φ) c)) ∧ Function.Injective (residueEmbed O Φ) ∧
      (∀ i : ℕ, ((residuePoly O Φ).map (residueEmbed O Φ)).IsRoot (rootBar O Φ ^ residueCard O ^ i))
      ∧ (∀ i j : ℕ, i < Φ.natDegree → j < Φ.natDegree → rootBar O Φ ^ residueCard O ^ i =
        rootBar O Φ ^ residueCard O ^ j → i = j) ∧ (residuePoly O Φ).map (residueEmbed O Φ) = ∏ i :
      Fin Φ.natDegree, conjugateFactor O Φ i ∧
      (∀ i j : Fin Φ.natDegree, i ≠ j → IsCoprime (conjugateFactor O Φ i) (conjugateFactor O Φ j)) := by sorry
