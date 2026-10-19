-- Prove2me | Theorems.Thm_TypeDensity_descend_block_mem_cell
-- name    : TypeDensity.descend_block_mem_cell
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:00:10.336025+00:00
-- url     : https://prove2.me/theorems/74312193-dc65-48c4-9aad-b7eddff456eb
-- title:
--   The descent of a block lies in the residue cell of `residuePoly Φ ^ r`, and its monic polynomial lifts to the conjugate product of the block.
-- statement:
--   The descent of a block lies in the residue cell of `residuePoly Φ ^ r`, and its monic polynomial lifts to the conjugate product of the block.
-- source:
--   TypeDensity/Unramified/FrobeniusDescent.lean#L759-L799

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_frobenius_residue_action
import Theorems.Thm_TypeDensity_frobenius_fixed_ring
import Theorems.Thm_TypeDensity_frobenius_pow_degree_eq_id
import Theorems.Thm_TypeDensity_unramified_is_domain
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

theorem TypeDensity.descend_block_mem_cell (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ) (b : Fin r → AdjoinRoot Φ)
    (hb : b ∈ blockCell O Φ r) :
    descendBlock O Φ r b ∈ residueCell O (Φ.natDegree * r) (residuePoly O Φ ^ r) ∧
      (monicPolyO (descendBlock O Φ r b)).map (AdjoinRoot.of Φ) =
        conjugateProduct O Φ (monicPolyO b) := by sorry
