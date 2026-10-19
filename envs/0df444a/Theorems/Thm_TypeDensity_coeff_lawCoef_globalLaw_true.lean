-- Prove2me | Theorems.Thm_TypeDensity_coeff_lawCoef_globalLaw_true
-- name    : TypeDensity.coeff_lawCoef_globalLaw_true
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:14:59.212681+00:00
-- url     : https://prove2.me/theorems/4ebdf2ca-cce7-4e20-a1f6-3da230c06ed0
-- title:
--   The `σ`-coefficient of the global projective law, read in `Coef`, is the rational function of `projectiveExpr n σ`.
-- statement:
--   The `σ`-coefficient of the global projective law, read in `Coef`, is the rational function of `projectiveExpr n σ`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L166-L170

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_lawWf_globalLaw
import Theorems.Thm_TypeDensity_coeff_lawCoef
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
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Log
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.coeff_lawCoef_globalLaw_true (n : ℕ) (σ : FactorType) :
    (lawCoef (globalLaw true n)).coeff σ = (projectiveExpr n σ).rational := by sorry
