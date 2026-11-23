-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_EqOneOfPowNear_eq_one_of_pow_near
-- name    : UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:09.796796+00:00
-- url     : https://prove2.me/theorems/bce85db1-408f-4b51-a348-2fa2fd39387f
-- title:
--   Eq One Of Pow Near: eq one of pow near
-- statement:
--   The Eq One Of Pow Near construction uses the eq one of pow near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EqOneOfPowNear.lean#L3-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EqOneOfPowNear.lean#L3-L32

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqOneOfPowNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near :
    ∀ (z : ℂ),
    (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by sorry
