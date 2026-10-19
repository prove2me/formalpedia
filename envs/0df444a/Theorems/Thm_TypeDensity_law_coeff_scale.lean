-- Prove2me | Theorems.Thm_TypeDensity_law_coeff_scale
-- name    : TypeDensity.law_coeff_scale
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:43.519214+00:00
-- url     : https://prove2.me/theorems/e58c0aa5-569e-47bf-a8dc-90f723d8ed7e
-- title:
--   Coefficients of a scaled law: `(x · L)_σ = x · L_σ`.
-- statement:
--   Coefficients of a scaled law: `(x · L)_σ = x · L_σ`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L635-L639

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_lawInterp_lawScale
import Theorems.Thm_TypeDensity_lawInterp_coeff
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

theorem TypeDensity.law_coeff_scale (x : Expr) (L : Law) (σ : FactorType) (q : ℚ) :
    (lawCoeff (lawScale x L) σ).eval q = x.eval q * (lawCoeff L σ).eval q := by sorry
