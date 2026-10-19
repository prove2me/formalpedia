-- Prove2me | Theorems.Thm_TypeDensity_selectBlock_spec
-- name    : TypeDensity.selectBlock_spec
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:44:11.06435+00:00
-- url     : https://prove2.me/theorems/bfb144cf-0d7a-4ee2-a8a3-fccbf5d1a5b4
-- title:
--   `selectBlock` picks block `0` of the Hensel splitting of the lift of `monicPolyO a`, which is the unique monic divisor of degree `r` reducing to `(X - θ̄) ^ r`.
-- statement:
--   `selectBlock` picks block `0` of the Hensel splitting of the lift of `monicPolyO a`, which is the unique monic divisor of degree `r` reducing to `(X - θ̄) ^ r`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L1010-L1059

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_hensel_family_exists
import Theorems.Thm_TypeDensity_hensel_factor_unique_of_dvd
import Theorems.Thm_TypeDensity_hensel_family_unique
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_unramified_is_dvr
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

theorem TypeDensity.selectBlock_spec (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (r : ℕ) (hδ : 0 < Φ.natDegree) (a : Fin (Φ.natDegree * r) → O)
    (ha : a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r)) :
    ∃ B : Fin Φ.natDegree → Polynomial (AdjoinRoot Φ), (∀ i, (B i).Monic) ∧
      (∀ i, (B i).natDegree = r) ∧
      (∀ i, (B i).map (baseReduce O Φ) = conjugateFactor O Φ i ^ r) ∧
      ∏ i, B i = (monicPolyO a).map (AdjoinRoot.of Φ) ∧
      (∀ B₀ : Polynomial (AdjoinRoot Φ), B₀.Monic → B₀.natDegree = r →
        B₀.map (baseReduce O Φ) = conjugateFactor O Φ 0 ^ r →
        B₀ ∣ (monicPolyO a).map (AdjoinRoot.of Φ) → B₀ = B ⟨0, hδ⟩) ∧
      selectBlock O Φ r a = coeffVec r (B ⟨0, hδ⟩) ∧
      monicPolyO (selectBlock O Φ r a) = B ⟨0, hδ⟩ := by sorry
