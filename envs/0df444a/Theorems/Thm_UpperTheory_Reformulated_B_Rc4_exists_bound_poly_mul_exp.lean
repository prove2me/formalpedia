-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Rc4_exists_bound_poly_mul_exp
-- name    : UpperTheory.Reformulated.B.Rc4.exists_bound_poly_mul_exp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:24:16.526814+00:00
-- url     : https://prove2.me/theorems/42e89015-5fe2-470b-9cdd-f285d30ac3ff
-- title:
--   Rc4: exists bound poly mul exp
-- statement:
--   The Rc4 construction uses the exists bound poly mul exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsBoundPolyMulExp.lean#L3-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsBoundPolyMulExp.lean#L3-L20

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsBoundPolyMulExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Rc4.exists_bound_poly_mul_exp :
    ∀ (c : ℝ),
    (0 : ℝ) < c →
      ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r → ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by sorry
