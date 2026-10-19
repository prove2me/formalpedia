-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_globalLaw_false
-- name    : TypeDensity.lawCoef_globalLaw_false
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:25:31.771581+00:00
-- url     : https://prove2.me/theorems/6549f492-c538-4af0-9685-f38ebb551243
-- title:
--   The global monic law is `q^{-n}` times the pattern sum `patternSum 0 1 n n`.
-- statement:
--   The global monic law is `q^{-n}` times the pattern sum `patternSum 0 1 n n`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L361-L369

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_lawCoef_residue_flatMap
import Theorems.Thm_TypeDensity_Expr_rational_inv
import Theorems.Thm_TypeDensity_Expr_rational_var
import Theorems.Thm_TypeDensity_lawCoef_lawScale
import Theorems.Thm_TypeDensity_Expr_rational_pow
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

theorem TypeDensity.lawCoef_globalLaw_false (n : ℕ) :
    lawCoef (globalLaw false n) = qpow (-(n : ℤ)) * patternSum 0 1 n n := by sorry
