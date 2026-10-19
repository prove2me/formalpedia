-- Prove2me | Theorems.Thm_TypeDensity_block_translation
-- name    : TypeDensity.block_translation
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:02.125402+00:00
-- url     : https://prove2.me/theorems/fec9ad4c-2bfd-49ef-8f8c-98c2cb47cd54
-- title:
--   Translation `X ↦ X + θ` maps the block cell bijectively onto the `X^r` cell and preserves congruences modulo powers of `m_O O_δ`.
-- statement:
--   Translation `X ↦ X + θ` maps the block cell bijectively onto the `X^r` cell and preserves congruences modulo powers of `m_O O_δ`.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L981-L1068

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
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
open Polynomial

theorem TypeDensity.block_translation (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)]
    (Φ : Polynomial O) (hΦ : IsUnramifiedLift O Φ) (r : ℕ) :
    Set.BijOn (translateBlock O Φ r) (blockCell O Φ r) (zeroCell O Φ r) ∧
      (∀ (L : ℕ) (b b' : Fin r → AdjoinRoot Φ), (∀ j, b j - b' j ∈ (baseIdeal O Φ) ^ L) ↔ ∀ j,
        translateBlock O Φ r b j - translateBlock O Φ r b' j ∈ (baseIdeal O Φ) ^ L) := by sorry
