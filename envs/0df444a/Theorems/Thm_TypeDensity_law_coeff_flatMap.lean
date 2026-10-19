-- Prove2me | Theorems.Thm_TypeDensity_law_coeff_flatMap
-- name    : TypeDensity.law_coeff_flatMap
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:47.352202+00:00
-- url     : https://prove2.me/theorems/8d87ad9c-da9b-43c3-b3f2-5a2efd9990df
-- title:
--   Coefficients are additive under concatenation, vanish on the empty law, and sum over a `flatMap`.
-- statement:
--   Coefficients are additive under concatenation, vanish on the empty law, and sum over a `flatMap`.
-- source:
--   TypeDensity/Formula/LawAlgebra.lean#L515-L527

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Theorems.Thm_TypeDensity_lawInterp_nil
import Theorems.Thm_TypeDensity_lawInterp_append
import Theorems.Thm_TypeDensity_lawInterp_flatMap
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

theorem TypeDensity.law_coeff_flatMap (α : Type) (xs : List α) (f : α → Law) (L M : Law) (σ : FactorType)
    (q : ℚ) :
    (lawCoeff (L ++ M) σ).eval q = (lawCoeff L σ).eval q + (lawCoeff M σ).eval q ∧
      (lawCoeff ([] : Law) σ).eval q = 0 ∧
      (lawCoeff (xs.flatMap f) σ).eval q = (xs.map fun x ↦ (lawCoeff (f x) σ).eval q).sum := by sorry
