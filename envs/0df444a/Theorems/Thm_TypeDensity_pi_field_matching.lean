-- Prove2me | Theorems.Thm_TypeDensity_pi_field_matching
-- name    : TypeDensity.pi_field_matching
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:42.976027+00:00
-- url     : https://prove2.me/theorems/68b65ab7-6e77-42a5-9329-bcc77789c7dc
-- title:
--   A `K`-algebra isomorphism between finite products of fields `∏ Lᵢ ≃ ∏ L'ⱼ` yields an injection `φ : ι → ι'` with `Lᵢ ≃ L'_{φ i}`.
-- statement:
--   A `K`-algebra isomorphism between finite products of fields `∏ Lᵢ ≃ ∏ L'ⱼ` yields an injection `φ : ι → ι'` with `Lᵢ ≃ L'_{φ i}`.
-- source:
--   TypeDensity/Algebra/FactorInvariant.lean#L204-L228

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_pi_field_maximal_ideals
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
open Polynomial

theorem TypeDensity.pi_field_matching (K : Type) [Field K] (ι ι' : Type) [Finite ι] [Finite ι']
    (L : ι → Type) [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
    (L' : ι' → Type) [∀ i, Field (L' i)] [∀ i, Algebra K (L' i)]
    (f : (∀ i, L i) ≃ₐ[K] (∀ j, L' j)) :
    ∃ φ : ι → ι', Function.Injective φ ∧ ∀ i, Nonempty (L i ≃ₐ[K] L' (φ i)) := by sorry
