-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r25a_pow_two_pow_sub_one_growth
-- name    : UpperTheory.Reformulated.B.P6.r25a.pow_two_pow_sub_one_growth
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:40.311414+00:00
-- url     : https://prove2.me/theorems/cdcba269-e294-4a6f-9336-f5579aff11b4
-- title:
--   r25a: pow two pow sub one growth
-- statement:
--   The r25a construction uses the pow two pow sub one growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/PowTwoPowSubOneGrowth.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/PowTwoPowSubOneGrowth.lean#L19-L31

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_PowTwoPowSubOneGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r25a

theorem UpperTheory.Reformulated.B.P6.r25a.pow_two_pow_sub_one_growth (z : ℂ) (hz : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) :
    ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by sorry
