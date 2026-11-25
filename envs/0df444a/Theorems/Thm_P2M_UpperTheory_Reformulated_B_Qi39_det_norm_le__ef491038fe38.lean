-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38
-- name    : P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:18.586271+00:00
-- url     : https://prove2.me/theorems/6482a3f6-a3a6-5085-bd02-5995a8398edf
-- title:
--   P2 M Upper Theory Reformulated B Qi39 det norm le  ef491038fe38: P2 M Upper Theory Reformulated B Qi39 det norm le  ef491038fe38
-- statement:
--   The P2 M Upper Theory Reformulated B Qi39 det norm le  ef491038fe38 construction uses the P2 M Upper Theory Reformulated B Qi39 det norm le  ef491038fe38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DetNormLe.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DetNormLe.lean#L7-L27

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38.{u_1} :
    ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] (A : Matrix n n ℂ) {m : ℝ},
      UpperTheory.Reformulated.B.Qi39.EB A m → ‖A.det‖ ≤ (↑(Fintype.card n).factorial : ℝ) * m ^ Fintype.card n := by sorry

alias «UpperTheory».«Reformulated».«B».«Qi39».«det_norm_le» := P2M_UpperTheory_Reformulated_B_Qi39_det_norm_le__ef491038fe38
