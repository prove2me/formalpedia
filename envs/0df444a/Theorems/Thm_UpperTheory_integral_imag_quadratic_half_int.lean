-- Prove2me | Theorems.Thm_UpperTheory_integral_imag_quadratic_half_int
-- name    : UpperTheory.integral_imag_quadratic_half_int
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:54.08321+00:00
-- url     : https://prove2.me/theorems/bc8394a3-e03a-4d82-918a-896d18c84e6a
-- title:
--   Upper Theory: integral imag quadratic half int
-- statement:
--   The Upper Theory construction uses the integral imag quadratic half int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralImagQuadraticHalfInt.lean#L98-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralImagQuadraticHalfInt.lean#L98-L136

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralImagQuadraticHalfInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial

theorem UpperTheory.integral_imag_quadratic_half_int :
    ∀ (E : Type) [Field E] [CharZero E] (d : ℕ) (s : E), Squarefree d → s ^ 2 = -(d : E) → ∀ z : E, z ∈ IntermediateField.adjoin ℚ ({s} : Set E) → IsIntegral ℤ z → ∃ x y : ℤ, Even (x - y) ∧ z = ((x : E) + (y : E) * s) / 2 := by sorry
