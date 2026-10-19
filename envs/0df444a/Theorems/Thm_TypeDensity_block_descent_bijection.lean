-- Prove2me | Theorems.Thm_TypeDensity_block_descent_bijection
-- name    : TypeDensity.block_descent_bijection
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:14:45.683649+00:00
-- url     : https://prove2.me/theorems/0618fab5-41fd-4437-9c79-e04a5c7d5ba5
-- title:
--   Frobenius descent: `selectBlock` is a bijection from the residue cell of `residuePoly Φ ^ r` over `O` onto the block cell over `O[X]/(Φ)`, with inverse `descendBlock`;
-- statement:
--   Frobenius descent: `selectBlock` is a bijection from the residue cell of `residuePoly Φ ^ r` over `O` onto the block cell over `O[X]/(Φ)`, with inverse `descendBlock`; the selected monic polynomial divides the lift of `monicPolyO a`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L1061-L1125

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_descend_block_mem_cell
import Theorems.Thm_TypeDensity_unramified_is_dvr
import Theorems.Thm_TypeDensity_block_conjugates
import Theorems.Thm_TypeDensity_selectBlock_spec
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

theorem TypeDensity.block_descent_bijection (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    (r : ℕ) :
    Set.BijOn (selectBlock O Φ r) (residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r))
      (blockCell O Φ r) ∧
    (∀ a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r),
      descendBlock O Φ r (selectBlock O Φ r a) = a) ∧
    (∀ b ∈ blockCell O Φ r, selectBlock O Φ r (descendBlock O Φ r b) = b) ∧
    (∀ a ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r),
      (monicPolyO (selectBlock O Φ r a)).Monic ∧
        monicPolyO (selectBlock O Φ r a) ∣ (monicPolyO a).map (AdjoinRoot.of Φ)) := by sorry
