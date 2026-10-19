-- Prove2me | Theorems.Thm_TypeDensity_law_coeff_prod_descend
-- name    : TypeDensity.law_coeff_prod_descend
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:19:07.824312+00:00
-- url     : https://prove2.me/theorems/8501159e-2799-4aca-ba2b-6dd424dd6c7a
-- title:
--   Coefficient formula for a product of descended laws `∏ⱼ lawDescend δⱼ Lⱼ`.
-- statement:
--   The coefficient formula for a product of descended laws `∏ⱼ lawDescend δⱼ Lⱼ` expresses each coefficient as a sum over type families `τ` with `σ = Σⱼ δⱼ·τⱼ` of the products of the coefficients of `Lⱼ` at `τⱼ` evaluated at `q^δⱼ`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L565-L605

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_law_coeff_descend
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

theorem TypeDensity.law_coeff_prod_descend (Ls : List (ℕ × Law)) (hδ : ∀ z ∈ Ls, 0 < z.1)
    (σ : FactorType) (q : ℚ) :
    (lawCoeff (lawProd (Ls.map fun z ↦ lawDescend z.1 z.2)) σ).eval q =
      ∑ τ ∈ Fintype.piFinset (fun j : Fin Ls.length ↦ ((Ls.get j).2.map Prod.fst).toFinset),
        (if σ = ∑ j, scaleType (Ls.get j).1 (τ j) then
          ∏ j, (lawCoeff (Ls.get j).2 (τ j)).eval (q ^ (Ls.get j).1) else 0) := by sorry
