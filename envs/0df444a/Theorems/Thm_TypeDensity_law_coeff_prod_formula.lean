-- Prove2me | Theorems.Thm_TypeDensity_law_coeff_prod_formula
-- name    : TypeDensity.law_coeff_prod_formula
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:18:59.370303+00:00
-- url     : https://prove2.me/theorems/d450dfbf-5ade-4934-86e4-7183fb84eb66
-- title:
--   Coefficient formula for a finite product of laws `∏ⱼ Dl j`, and vanishing of the coefficients of a law at types that do not occur in it.
-- statement:
--   This gives the coefficient formula for a finite product of laws `∏ⱼ Dl j`, and the vanishing of the coefficients of a law at types that do not occur in it.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L607-L633

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_lawInterp_coeff
import Theorems.Thm_TypeDensity_law_coeff_mul
import Theorems.Thm_TypeDensity_sum_piFinset_succ
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

theorem TypeDensity.law_coeff_prod_formula (L : ℕ) (Dl : Fin L → Law) (σ : FactorType) (q : ℚ) :
    ((lawCoeff (lawProd (List.ofFn Dl)) σ).eval q =
        ∑ τ ∈ Fintype.piFinset (fun j ↦ ((Dl j).map Prod.fst).toFinset),
          (if σ = ∑ j, τ j then ∏ j, (lawCoeff (Dl j) (τ j)).eval q else 0)) ∧
      ∀ (M : Law) (τ : FactorType), τ ∉ (M.map Prod.fst).toFinset →
        (lawCoeff M τ).eval q = 0 := by sorry
