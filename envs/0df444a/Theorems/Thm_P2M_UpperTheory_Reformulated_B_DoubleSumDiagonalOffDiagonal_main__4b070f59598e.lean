-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_DoubleSumDiagonalOffDiagonal_main__4b070f59598e
-- name    : P2M_UpperTheory_Reformulated_B_DoubleSumDiagonalOffDiagonal_main__4b070f59598e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:21:03.227792+00:00
-- url     : https://prove2.me/theorems/025cfece-3597-4f98-aae6-a21d2099e01e
-- title:
--   P2 M Upper Theory Reformulated B Double Sum Diagonal Off Diagonal main  4b070f59598e: P2 M Upper Theory Reformulated B Double Sum Diagonal Off Diagonal main  4b070f59598e
-- statement:
--   The P2 M Upper Theory Reformulated B Double Sum Diagonal Off Diagonal main  4b070f59598e construction uses the P2 M Upper Theory Reformulated B Double Sum Diagonal Off Diagonal main  4b070f59598e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FirstStatementB.lean#L3-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FirstStatementB.lean#L3-L36

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FirstStatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_DoubleSumDiagonalOffDiagonal_main__4b070f59598e.{u_3} :
    ∀ {n : ℕ} {M : Type u_3} [inst : AddCommMonoid M]
    (F : Fin n → Fin n → M),
    ∑ a : Fin n, ∑ b : Fin n, F a b =
      ∑ a : Fin n, F a a + ∑ a : Fin n, ∑ b : Fin n, if a < b then F a b + F b a else (0 : M) := by sorry

alias «UpperTheory».«Reformulated».«B».«DoubleSumDiagonalOffDiagonal».«main» := P2M_UpperTheory_Reformulated_B_DoubleSumDiagonalOffDiagonal_main__4b070f59598e
