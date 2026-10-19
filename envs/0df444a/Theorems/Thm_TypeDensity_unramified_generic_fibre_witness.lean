-- Prove2me | Theorems.Thm_TypeDensity_unramified_generic_fibre_witness
-- name    : TypeDensity.unramified_generic_fibre_witness
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:01:22.044362+00:00
-- url     : https://prove2.me/theorems/b9271e52-ad4b-4bfd-ae3b-2ba359828531
-- title:
--   In the unramified situation of `unramified_fraction_base_change`, a presentation of the `Oδ`-generic fibre of an `Oδ`-algebra `B` as a product of fields `Lᵢ` induces compatible `K`- and `O`-structures
-- statement:
--   In the unramified situation of `unramified_fraction_base_change`, a presentation of the `Oδ`-generic fibre of an `Oδ`-algebra `B` as a product of fields `Lᵢ` induces compatible `K`- and `O`-structures on the `Lᵢ` and a presentation of the `O`-generic fibre of `B`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L579-L642

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Theorems.Thm_TypeDensity_unramified_fraction_base_change
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
set_option autoImplicit false

open TypeDensity
open scoped TensorProduct
open Polynomial IsLocalRing

theorem TypeDensity.unramified_generic_fibre_witness (O Oδ : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CommRing Oδ] [IsDomain Oδ] [IsDiscreteValuationRing Oδ]
    [Algebra O Oδ] [Module.Finite O Oδ] [Module.Free O Oδ] (δ : ℕ) (hrank : Module.finrank O Oδ = δ)
    (pi : O) (hpi : Irreducible pi) (hpiδ : Irreducible (algebraMap O Oδ pi))
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] (B : Type)
    [CommRing B] [Algebra O B] [Algebra Oδ B] [IsScalarTower O Oδ B] (ι : Type)
    (L : ι → Type) [∀ i, Field (L i)] [∀ i, Algebra (BaseField Oδ) (L i)] [∀ i, Algebra Oδ (L i)]
    [∀ i, IsScalarTower Oδ (BaseField Oδ) (L i)] [∀ i, FiniteDimensional (BaseField Oδ) (L i)]
    (e : TensorProduct Oδ (BaseField Oδ) B ≃ₐ[BaseField Oδ] (∀ i, L i)) :
    ∃ (_ : ∀ i, Algebra (BaseField O) (L i)) (_ : ∀ i, Algebra O (L i))
      (_ : ∀ i, IsScalarTower O (BaseField O) (L i)) (_ : ∀ i, IsScalarTower O Oδ (L i))
      (_ : ∀ i, FiniteDimensional (BaseField O) (L i))
      (_ : TensorProduct O (BaseField O) B ≃ₐ[BaseField O] (∀ i, L i)), True := by sorry
