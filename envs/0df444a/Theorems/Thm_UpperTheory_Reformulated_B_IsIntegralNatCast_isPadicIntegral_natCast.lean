-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_IsIntegralNatCast_isPadicIntegral_natCast
-- name    : UpperTheory.Reformulated.B.IsIntegralNatCast.isPadicIntegral_natCast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:24.561252+00:00
-- url     : https://prove2.me/theorems/22081d47-0f39-4b20-921b-23387781f517
-- title:
--   Is Integral Nat Cast: is Padic Integral nat Cast
-- statement:
--   The Is Integral Nat Cast construction uses the is Padic Integral nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsIntegralNatCast.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IsIntegralNatCast.lean#L7-L10

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsIntegralNatCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.IsIntegralNatCast.isPadicIntegral_natCast :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (n : ℕ), UpperTheory.Reformulated.B.IsIntegralNatCast.IsIntP (↑n : ℂ_[p]) := by sorry
