-- Prove2me | Theorems.Thm_TypeDensity_algebra_type_pi
-- name    : TypeDensity.algebra_type_pi
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:32:09.459431+00:00
-- url     : https://prove2.me/theorems/281e57bd-9ff9-4b99-8b1c-d9e10334e977
-- title:
--   The type of a finite product of algebras is the sum of their types.
-- statement:
--   The type of a finite product of algebras is the sum of their types.
-- source:
--   TypeDensity/Algebra/AlgebraType.lean#L426-L443

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

theorem TypeDensity.algebra_type_pi (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (B : Fin n → Type)
    [∀ j, CommRing (B j)] [∀ j, Algebra O (B j)] (σ : Fin n → FactorType)
    (h : ∀ j, HasAlgebraType O (B j) (σ j)) : HasAlgebraType O (∀ j, B j) (∑ j, σ j) := by sorry
