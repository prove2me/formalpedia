-- Prove2me | Theorems.Thm_TypeDensity_algebra_type_of_generic_fibre_equiv
-- name    : TypeDensity.algebra_type_of_generic_fibre_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:30:26.847001+00:00
-- url     : https://prove2.me/theorems/ec712502-d609-4989-8285-8ba8303fc8a4
-- title:
--   Algebra types only depend on the generic fibre: an isomorphism `K ⊗_O A ≃ K ⊗_O B` transports the type of `B` to `A`.
-- statement:
--   Algebra types only depend on the generic fibre: an isomorphism `K ⊗_O A ≃ K ⊗_O B` transports the type of `B` to `A`.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L417-L424

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
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

theorem TypeDensity.algebra_type_of_generic_fibre_equiv (O : Type) [CommRing O] [IsDomain O] (A B : Type)
    [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
    (e : TensorProduct O (BaseField O) A ≃ₐ[BaseField O] TensorProduct O (BaseField O) B)
    (σ : FactorType) (h : HasAlgebraType O B σ) : HasAlgebraType O A σ := by sorry
