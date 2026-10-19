-- Prove2me | Theorems.Thm_TypeDensity_lawCoef_globalLaw_true
-- name    : TypeDensity.lawCoef_globalLaw_true
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:25:11.415531+00:00
-- url     : https://prove2.me/theorems/b5b44032-1f62-4104-bd3e-4f9c7b5bb133
-- title:
--   The global projective law is the pattern sum `patternSum 1 1 n n` divided by `1 + q + ⋯ + qⁿ`.
-- statement:
--   The global projective law is the pattern sum `patternSum 1 1 n n` divided by `1 + q + ⋯ + qⁿ`.
-- source:
--   TypeDensity/Reciprocity/Patterns.lean#L371-L380

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Definitions.Def_TypeDensity_Reciprocity_Defs
import Definitions.Def_TypeDensity_Reciprocity_Quantum
import Definitions.Def_TypeDensity_Reciprocity_Patterns
import Theorems.Thm_TypeDensity_lawCoef_residue_flatMap
import Theorems.Thm_TypeDensity_Expr_rational_inv
import Theorems.Thm_TypeDensity_lawCoef_lawScale
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

theorem TypeDensity.lawCoef_globalLaw_true (n : ℕ) :
    lawCoef (globalLaw true n) =
      scalar (((projectiveNormalizer n).rational)⁻¹) * patternSum 1 1 n n := by sorry
