-- Prove2me | Theorems.Thm_TypeDensity_product_division_equiv
-- name    : TypeDensity.product_division_equiv
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:54.723558+00:00
-- url     : https://prove2.me/theorems/f3f62fa2-e3ee-471f-958f-3db221ce371d
-- title:
--   Division equivalences in the factors assemble into a division equivalence on the product.
-- statement:
--   Division equivalences in the factors assemble into a division equivalence on the product.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L1052-L1101

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
set_option autoImplicit false

open TypeDensity
open MeasureTheory
open scoped BigOperators ENNReal

theorem TypeDensity.product_division_equiv (O : Type) [CommRing O] (ι : Type) (Oj : ι → Type)
    [∀ j, CommRing (Oj j)] [∀ j, Algebra O (Oj j)] (R : ι → Type) [∀ j, CommRing (R j)]
    [∀ j, Algebra O (R j)] [∀ j, Algebra (Oj j) (R j)] [∀ j, IsScalarTower O (Oj j) (R j)]
    (nn : ι → ℕ) (n : ℕ) (ρ : (Fin n → O) ≃ₗ[O] (∀ j, Fin (nn j) → Oj j))
    (bc' : ∀ j, Fin (nn j) → R j) (bc : Fin n → ∀ j, R j)
    (hcompat : ∀ (w : Fin n → O) (j : ι), coordinateLift bc w j = coordinateLift (bc' j) (ρ w j))
    (g : ∀ j, R j) (E' : ∀ j, R j ≃ₗ[Oj j] ((Fin (nn j) → Oj j) × R j))
    (hE' : ∀ j w, (E' j).symm w = divisionMap (g j) (bc' j) w) :
    (letI : Module O (∀ j, R j) := Algebra.toModule;
      ∃ E : (∀ j, R j) ≃ₗ[O] ((Fin n → O) × ∀ j, R j), ∀ w, E.symm w = divisionMap g bc w) := by sorry
