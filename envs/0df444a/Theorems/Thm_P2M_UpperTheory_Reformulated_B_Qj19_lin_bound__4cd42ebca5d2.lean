-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qj19_lin_bound__4cd42ebca5d2
-- name    : P2M_UpperTheory_Reformulated_B_Qj19_lin_bound__4cd42ebca5d2
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:26.512647+00:00
-- url     : https://prove2.me/theorems/894bc1af-6d18-5ac2-9e09-ca02a4f6cf95
-- title:
--   P2 M Upper Theory Reformulated B Qj19 lin bound  4cd42ebca5d2: P2 M Upper Theory Reformulated B Qj19 lin bound  4cd42ebca5d2
-- statement:
--   The P2 M Upper Theory Reformulated B Qj19 lin bound  4cd42ebca5d2 construction uses the P2 M Upper Theory Reformulated B Qj19 lin bound  4cd42ebca5d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LinBound.lean#L3-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LinBound.lean#L3-L19

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LinBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_Qj19_lin_bound__4cd42ebca5d2.{u_1} :
    ∀ {ι : Type u_1} [Fintype ι] [DecidableEq ι] (L : Matrix ι ι ℂ →ₗ[ℂ] ℂ),
    ∃ (K : ℝ),
      (0 : ℝ) ≤ K ∧ ∀ (B : Matrix ι ι ℂ) (C : ℝ), (∀ (i j : ι), ‖B i j‖ ≤ C) → ‖(L : Matrix ι ι ℂ → ℂ) B‖ ≤ K * C := by sorry

alias «UpperTheory».«Reformulated».«B».«Qj19».«lin_bound».«» := P2M_UpperTheory_Reformulated_B_Qj19_lin_bound__4cd42ebca5d2
