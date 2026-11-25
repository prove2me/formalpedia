-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b
-- name    : P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:21:22.50699+00:00
-- url     : https://prove2.me/theorems/c6a07db2-9a50-5829-a3f5-2f3d2a92aeb3
-- title:
--   P2 M Upper Theory Reformulated B Qh19 trace pow eq zero of le dim  a8f51753728b: P2 M Upper Theory Reformulated B Qh19 trace pow eq zero of le dim  a8f51753728b
-- statement:
--   The P2 M Upper Theory Reformulated B Qh19 trace pow eq zero of le dim  a8f51753728b construction uses the P2 M Upper Theory Reformulated B Qh19 trace pow eq zero of le dim  a8f51753728b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TracePowEqZeroOfLeDim.lean#L3-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TracePowEqZeroOfLeDim.lean#L3-L28

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TracePowEqZeroOfLeDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b.{u_1} :
    ∀ {K : Type u_1}
    [inst : Field K] (r : ℕ) (N : Matrix (Fin r) (Fin r) K),
    (∀ (k : ℕ), (1 : ℕ) ≤ k → k ≤ r → (N ^ k).trace = (0 : K)) → ∀ (k : ℕ), (1 : ℕ) ≤ k → (N ^ k).trace = (0 : K) := by sorry

alias «UpperTheory».«Reformulated».«B».«Qh19».«trace_pow_eq_zero_of_le_dim».«» := P2M_UpperTheory_Reformulated_B_Qh19_trace_pow_eq_zero_of_le_dim__a8f51753728b
