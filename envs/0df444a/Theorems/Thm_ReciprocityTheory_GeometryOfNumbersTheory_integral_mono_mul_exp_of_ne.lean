-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integral_mono_mul_exp_of_ne
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.integral_mono_mul_exp_of_ne
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:53:29.791347+00:00
-- url     : https://prove2.me/theorems/8a60e853-94fb-4317-8fd6-bf45f3d7c966
-- title:
--   Geometry Of Numbers Theory: integral mono mul exp of ne
-- statement:
--   The Geometry Of Numbers Theory construction uses the integral mono mul exp of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/GaussSt.lean#L142-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/GaussSt.lean#L142-L148

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.integral_mono_mul_exp_of_ne {N : ℕ} {a b : Fin N → ℕ} (hab : a ≠ b) {t : ℝ} (ht : 0 < t) :
    ∫ z : Fin N → ℂ, starRingEnd ℂ (monoC a z) * monoC b z * (Real.exp (-(t * sqN z)) : ℂ) = 0 := by sorry
