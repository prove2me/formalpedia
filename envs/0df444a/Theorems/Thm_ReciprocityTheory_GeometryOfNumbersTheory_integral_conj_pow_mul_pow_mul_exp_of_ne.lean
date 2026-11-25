-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_conj_pow_mul_pow_mul_exp_of_ne
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.integral_conj_pow_mul_pow_mul_exp_of_ne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:54:14.699939+00:00
-- url     : https://prove2.me/theorems/ca391234-9281-4d7b-81c0-f94b95bd999a
-- title:
--   Geometry Of Numbers Theory: integral conj pow mul pow mul exp of ne
-- statement:
--   The Geometry Of Numbers Theory construction uses the integral conj pow mul pow mul exp of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/GaussSt.lean#L99-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/GaussSt.lean#L99-L101

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory
open Set Complex

theorem ReciprocityTheory.GeometryOfNumbersTheory.integral_conj_pow_mul_pow_mul_exp_of_ne {a b : ℕ} (hab : a ≠ b) (t : ℝ) :
    ∫ z : ℂ, starRingEnd ℂ (z ^ a) * z ^ b * (Real.exp (-(t * ‖z‖ ^ 2)) : ℂ) = 0 := by sorry
