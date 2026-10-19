-- Prove2me | Theorems.Thm_TypeDensity_product_coordinates_exist
-- name    : TypeDensity.product_coordinates_exist
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:08.299237+00:00
-- url     : https://prove2.me/theorems/c66145ef-f568-4812-b699-57e8795d5c1f
-- title:
--   Coordinates on a finite product of free extensions: a measurable `O`-linear equivalence `O^n ≃ ∏ⱼ Oⱼ^(nⱼ)` (with `n = ∑ δⱼ nⱼ`) and representatives `bc` compatible with given representatives `bc' j` i
-- statement:
--   Coordinates on a finite product of free extensions: there is a measurable `O`-linear equivalence `O^n ≃ ∏ⱼ Oⱼ^(nⱼ)` (with `n = ∑ δⱼ nⱼ`) and representatives `bc` compatible with given representatives `bc' j` in each factor.
-- source:
--   TypeDensity/Measure/HenselProducts.lean#L981-L1050

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

theorem TypeDensity.product_coordinates_exist (O : Type) [CommRing O] [MeasurableSpace O] (ι : Type) [Fintype ι]
    (Oj : ι → Type) [∀ j, CommRing (Oj j)] [∀ j, Algebra O (Oj j)] [∀ j, MeasurableSpace (Oj j)]
    (R : ι → Type) [∀ j, CommRing (R j)] [∀ j, Algebra O (R j)] [∀ j, Algebra (Oj j) (R j)]
    [∀ j, IsScalarTower O (Oj j) (R j)] (δ nn : ι → ℕ) (pc : ∀ j, Oj j ≃ₗ[O] (Fin (δ j) → O))
    (hpc : ∀ j, Measurable (pc j)) (hpc' : ∀ j, Measurable (pc j).symm) (n : ℕ)
    (hn : ∑ j, δ j * nn j = n) (bc' : ∀ j, Fin (nn j) → R j) :
    ∃ (ρ : (Fin n → O) ≃ₗ[O] (∀ j, Fin (nn j) → Oj j)) (bc : Fin n → ∀ j, R j), Measurable ρ ∧
      Measurable ρ.symm ∧ ∀ (w : Fin n → O) (j : ι), coordinateLift bc w j =
      coordinateLift (bc' j) (ρ w j) := by sorry
