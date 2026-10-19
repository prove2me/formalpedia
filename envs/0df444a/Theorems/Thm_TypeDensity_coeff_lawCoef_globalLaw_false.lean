-- Prove2me | Theorems.Thm_TypeDensity_coeff_lawCoef_globalLaw_false
-- name    : TypeDensity.coeff_lawCoef_globalLaw_false
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:15:03.254609+00:00
-- url     : https://prove2.me/theorems/e9bf849f-970e-4869-b9f9-d9f1a49da55c
-- title:
--   The `σ`-coefficient of the global monic law, read in `Coef`, is the rational function of `monicExpr n σ`.
-- statement:
--   The `σ`-coefficient of the global monic law, read in `Coef`, is the rational function of `monicExpr n σ`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L160-L164

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

theorem TypeDensity.coeff_lawCoef_globalLaw_false (n : ℕ) (σ : FactorType) :
    (lawCoef (globalLaw false n)).coeff σ = (monicExpr n σ).rational := by sorry
