-- Prove2me | Theorems.Thm_TypeDensity_strict_quotient_map_exists
-- name    : TypeDensity.strict_quotient_map_exists
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:55.52785+00:00
-- url     : https://prove2.me/theorems/da55da8c-a4fa-40be-b2f8-b58c4696b4dc
-- title:
--   If `alpha f = e ^ d * g`, then `h ↦ c * alpha h` descends to an `O`-linear map `R ⧸ (f) → C ⧸ (g)`.
-- statement:
--   If `alpha f = e ^ d * g`, then `h ↦ c * alpha h` descends to an `O`-linear map `R ⧸ (f) → C ⧸ (g)`.
-- source:
--   TypeDensity/Blowup/StrictNormalizer.lean#L1040-L1060

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
import Definitions.Def_TypeDensity_Surfaces_TruncatedSeries
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
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Algebra.Group.NatPowAssoc
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.strict_quotient_map_exists (O R C : Type) [CommRing O] [CommRing R] [CommRing C]
    [Algebra O R] [Algebra O C] (alpha : R →ₐ[O] C) (f : R) (g e c : C) (d : ℕ)
    (hf : alpha f = e ^ d * g) :
    ∃ phi : (R ⧸ Ideal.span {f}) →ₗ[O] (C ⧸ Ideal.span {g}), ∀ h : R, phi
      (Ideal.Quotient.mk (Ideal.span {f}) h) = Ideal.Quotient.mk (Ideal.span {g})
          (c * alpha h) := by sorry
