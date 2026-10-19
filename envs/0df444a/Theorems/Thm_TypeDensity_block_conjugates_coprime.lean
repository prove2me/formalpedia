-- Prove2me | Theorems.Thm_TypeDensity_block_conjugates_coprime
-- name    : TypeDensity.block_conjugates_coprime
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:15.00098+00:00
-- url     : https://prove2.me/theorems/78814797-0578-4537-a74e-7b31f0e0f3ed
-- title:
--   Distinct Frobenius conjugates of the monic polynomial of a block are coprime over the fraction field of `O[X]/(Φ)`.
-- statement:
--   Distinct Frobenius conjugates of the monic polynomial of a block are coprime over the fraction field of `O[X]/(Φ)`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L930-L947

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_coprime_of_coprime_residue_dvr
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_unramified_is_dvr
import Theorems.Thm_TypeDensity_map_frobeniusIter_baseReduce
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

theorem TypeDensity.block_conjugates_coprime (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    [Finite (IsLocalRing.ResidueField O)] (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ)
    [IsDomain (AdjoinRoot Φ)] (r : ℕ) (b : Fin r → AdjoinRoot Φ) (hb : b ∈ blockCell O Φ r) :
    ∀ i j : Fin Φ.natDegree, i ≠ j →
      IsCoprime (((monicPolyO b).map (frobeniusIter O Φ i).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ))))
        (((monicPolyO b).map (frobeniusIter O Φ j).toRingHom).map
          (algebraMap (AdjoinRoot Φ) (BaseField (AdjoinRoot Φ)))) := by sorry
