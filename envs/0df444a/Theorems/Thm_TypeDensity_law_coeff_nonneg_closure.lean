-- Prove2me | Theorems.Thm_TypeDensity_law_coeff_nonneg_closure
-- name    : TypeDensity.law_coeff_nonneg_closure
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:28.453081+00:00
-- url     : https://prove2.me/theorems/47538627-1a1d-4f04-ac74-b9e5be398ccf
-- title:
--   Nonnegativity of law coefficients at `q` is preserved by scaling by nonnegative expressions, products, finite products, flat maps and descents, and holds for atoms and the unit law;
-- statement:
--   Nonnegativity of law coefficients at `q` is preserved by scaling by nonnegative expressions, products, finite products, flat maps and descents, and holds for atoms and the unit law; the empty law has zero coefficients.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L641-L694

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_law_coeff_descend
import Theorems.Thm_TypeDensity_law_coeff_flatMap
import Theorems.Thm_TypeDensity_law_coeff_mul
import Theorems.Thm_TypeDensity_law_coeff_scale
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
set_option autoImplicit false

open TypeDensity
open scoped BigOperators ENNReal

theorem TypeDensity.law_coeff_nonneg_closure (q : ℚ) :
    (∀ (x : Expr) (L : Law), 0 ≤ x.eval q → (∀ σ : FactorType, 0 ≤ (lawCoeff L σ).eval q) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (lawScale x L) σ).eval q) ∧
    (∀ L M : Law, (∀ σ : FactorType, 0 ≤ (lawCoeff L σ).eval q) →
      (∀ σ : FactorType, 0 ≤ (lawCoeff M σ).eval q) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (lawMul L M) σ).eval q) ∧
    (∀ Ls : List Law, (∀ L ∈ Ls, (∀ σ : FactorType, 0 ≤ (lawCoeff L σ).eval q)) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (lawProd Ls) σ).eval q) ∧
    (∀ (α : Type) (xs : List α) (f : α → Law),
      (∀ x ∈ xs, ∀ σ : FactorType, 0 ≤ (lawCoeff (f x) σ).eval q) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (xs.flatMap f) σ).eval q) ∧
    (∀ (δ : ℕ), 0 < δ → ∀ L : Law, (∀ σ : FactorType, 0 ≤ (lawCoeff L σ).eval (q ^ δ)) →
      ∀ σ : FactorType, 0 ≤ (lawCoeff (lawDescend δ L) σ).eval q) ∧
    (∀ (a f : ℕ) (σ : FactorType), 0 ≤ (lawCoeff (lawAtom a f) σ).eval q) ∧
    (∀ σ : FactorType, 0 ≤ (lawCoeff lawOne σ).eval q) ∧
    (∀ σ : FactorType, (lawCoeff ([] : Law) σ).eval q = 0) := by sorry
