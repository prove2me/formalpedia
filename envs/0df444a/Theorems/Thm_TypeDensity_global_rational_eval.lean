-- Prove2me | Theorems.Thm_TypeDensity_global_rational_eval
-- name    : TypeDensity.global_rational_eval
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T15:14:59.364292+00:00
-- url     : https://prove2.me/theorems/6f3db34f-6650-4952-9906-710b5e7973b0
-- title:
--   The rational functions of the monic and projective expressions evaluate correctly at prime powers.
-- statement:
--   The rational functions of the monic and projective expressions evaluate correctly at prime powers.
-- source:
--   TypeDensity/Formula/RationalEval.lean#L54-L64

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Formula_StateCombinatorics
import Theorems.Thm_TypeDensity_expression_fraction
import Theorems.Thm_TypeDensity_prime_power_ge_two
import Theorems.Thm_TypeDensity_global_coefficients_safe
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
set_option autoImplicit false

open TypeDensity

theorem TypeDensity.global_rational_eval (n : ℕ) (σ : FactorType) :
    ∀ q : ℕ, PrimePower q → RatFunc.eval (RingHom.id ℚ) q (monicExpr n σ).rational =
        (monicExpr n σ).eval q ∧ RatFunc.eval (RingHom.id ℚ) q (projectiveExpr n σ).rational =
        (projectiveExpr n σ).eval q := by sorry
