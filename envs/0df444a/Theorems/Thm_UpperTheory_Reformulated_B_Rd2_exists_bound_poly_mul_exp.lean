-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Rd2_exists_bound_poly_mul_exp
-- name    : UpperTheory.Reformulated.B.Rd2.exists_bound_poly_mul_exp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:08:56.52503+00:00
-- url     : https://prove2.me/theorems/812a403a-76f9-4908-b675-622109b251e4
-- title:
--   Rd2: exists bound poly mul exp
-- statement:
--   The Rd2 construction uses the exists bound poly mul exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsBoundPolyMulExpAlt.lean#L3-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsBoundPolyMulExpAlt.lean#L3-L20

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsBoundPolyMulExpAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Rd2.exists_bound_poly_mul_exp :
    ∀ (c : ℝ),
    (0 : ℝ) < c →
      ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r → ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by sorry
