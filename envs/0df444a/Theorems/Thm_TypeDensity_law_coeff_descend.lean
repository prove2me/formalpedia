-- Prove2me | Theorems.Thm_TypeDensity_law_coeff_descend
-- name    : TypeDensity.law_coeff_descend
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:29:08.825676+00:00
-- url     : https://prove2.me/theorems/2e0cff7e-837c-460a-8e81-3b468ae359ab
-- title:
--   Coefficients of a descended law: `lawDescend δ L` has coefficient `L_τ(q^δ)` at `scaleType δ τ` and vanishing coefficients at types not of this form.
-- statement:
--   Coefficients of a descended law: `lawDescend δ L` has coefficient `L_τ(q^δ)` at `scaleType δ τ` and vanishing coefficients at types not of this form.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L428-L443

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
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

theorem TypeDensity.law_coeff_descend (δ : ℕ) (hδ : 0 < δ) (L : Law) (τ : FactorType) (q : ℚ) :
    (lawCoeff (lawDescend δ L) (scaleType δ τ)).eval q = (lawCoeff L τ).eval (q ^ δ) ∧
      ∀ σ : FactorType, (∀ τ' : FactorType, σ ≠ scaleType δ τ') →
        (lawCoeff (lawDescend δ L) σ).eval q = 0 := by sorry
