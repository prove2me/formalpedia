-- Prove2me | Theorems.Thm_TypeDensity_block_conjugates
-- name    : TypeDensity.block_conjugates
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:05.610883+00:00
-- url     : https://prove2.me/theorems/44d68e5b-a876-4348-a46e-7df76bf67ebd
-- title:
--   If monic polynomials `B i` over `O[X]/(Φ)` of degree `r`, with `B i` reducing to `(X - θ̄ ^ (q ^ i)) ^ r`, multiply to the lift of `monicPolyO a`, then each `B i` is the `i`-th Frobenius conjugate of
-- statement:
--   If monic polynomials `B i` over `O[X]/(Φ)` of degree `r`, with `B i` reducing to `(X - θ̄ ^ (q ^ i)) ^ r`, multiply to the lift of `monicPolyO a`, then each `B i` is the `i`-th Frobenius conjugate of `B 0`.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L890-L928

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_hensel_factor_unique_of_dvd
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

theorem TypeDensity.block_conjugates (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ) (a : Fin (Φ.natDegree * r) → O)
    (hδ : 0 < Φ.natDegree)
    (B : Fin Φ.natDegree → Polynomial (AdjoinRoot Φ)) (hB : ∀ i, (B i).Monic)
    (hBr : ∀ i, (B i).map (baseReduce O Φ) = conjugateFactor O Φ i ^ r)
    (hBp : ∏ i, B i = (monicPolyO a).map (AdjoinRoot.of Φ)) :
    ∀ i : Fin Φ.natDegree, B i = (B ⟨0, hδ⟩).map (frobeniusIter O Φ i).toRingHom := by sorry
