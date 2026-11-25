-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Yoa2_mul_left_cancel_of_det_ne_zero__dceecbbc2fba
-- name    : P2M_UpperTheory_Reformulated_B_Yoa2_mul_left_cancel_of_det_ne_zero__dceecbbc2fba
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:22:07.909746+00:00
-- url     : https://prove2.me/theorems/2bf530b4-6f04-4be6-9514-ef0a31470cc2
-- title:
--   P2 M Upper Theory Reformulated B Yoa2 mul left cancel of det ne zero  dceecbbc2fba: P2 M Upper Theory Reformulated B Yoa2 mul left cancel of det ne zero  dceecbbc2fba
-- statement:
--   The P2 M Upper Theory Reformulated B Yoa2 mul left cancel of det ne zero  dceecbbc2fba construction uses the P2 M Upper Theory Reformulated B Yoa2 mul left cancel of det ne zero  dceecbbc2fba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MulLeftCancelOfDetNeZero.lean#L3-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MulLeftCancelOfDetNeZero.lean#L3-L14

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulLeftCancelOfDetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Yoa2_mul_left_cancel_of_det_ne_zero__dceecbbc2fba.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] [IsDomain R] {n : ℕ} {A X Y : Matrix (Fin n) (Fin n) R},
      A.det ≠ (0 : R) → A * X = A * Y → X = Y := by sorry

alias «UpperTheory».«Reformulated».«B».«Yoa2».«mul_left_cancel_of_det_ne_zero».«» := P2M_UpperTheory_Reformulated_B_Yoa2_mul_left_cancel_of_det_ne_zero__dceecbbc2fba
