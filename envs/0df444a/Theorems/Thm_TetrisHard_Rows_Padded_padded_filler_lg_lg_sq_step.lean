-- Prove2me | Theorems.Thm_TetrisHard_Rows_Padded_padded_filler_lg_lg_sq_step
-- name    : TetrisHard.Rows.Padded.padded_filler_lg_lg_sq_step
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:28:39.971214+00:00
-- url     : https://prove2.me/theorems/870c7763-bae0-489a-916e-204b73890bc7
-- title:
--   Appendix C.2 — filler suffix [LG, LG, Sq] transition from trigger-happy state
-- statement:
--   Let $R$ be a reasonable rotation model and let $s \le s'$ and $H' \ge 0$. Suppose bucket $j_0 < s$ of $U_2$ satisfies $\mathrm{TriggerHappyAt}(U_2,j_0,H',h_{\mathrm{th}})$ and every $k \ne j_0$ satisfies $\mathrm{UnpreppedAt}(U_2,k,H',h(k))$. Then any zero-waste bucket play of the three-piece filler suffix $[\mathrm{LG},\mathrm{LG},\mathrm{Sq}]$ reaching an $\mathrm{AllFillableStrict}$ board $U'$ satisfies
--   $$\mathrm{OneOverflatState}(U',s,H',j_0,h_{\mathrm{th}}+2,\mathbf{h}) \;\lor\; \exists\, j_{\mathrm{dp}} < s,\ \mathrm{DeadTriggerState}(U',s,H',j_{\mathrm{dp}},j_0,h_{\mathrm{th}},\mathbf{h}).$$
--
--   Either all three pieces land in $j_0$ and complete a $+6$ height increment on the active overflat bucket, or all three land in a single other bucket $j_{\mathrm{dp}} \ne j_0$ and create a dead plateau alongside the unresolved trigger-happy bucket $j_0$ (Propositions C.2-C.3, C.8, C.10-C.12, C.17-C.18, C.20, C.28-C.29, C.31, and C.33-C.34).
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 5.3-5.4 (pp. 12-18), Section 6.2 (pp. 19-21), and Appendix C.1-C.2 (pp. 25-33), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_PaddedSoundness

namespace TetrisHard.Rows.Padded

theorem padded_filler_lg_lg_sq_step
    (R : Rotation) (hReason : Reasonable R) (s s' H' : ℕ) (hs_le : s ≤ s')
    (U₂ U' : Board) (us : List PieceState) (j₀ : Fin s) (h_th : ℕ) (h : Fin s → ℕ)
    (hth0 : TriggerHappyAt U₂ j₀.val H' h_th)
    (hunp0 : ∀ k : Fin s, k ≠ j₀ → UnpreppedAt U₂ k.val H' (h k))
    (hp : NoRGSeqPlay R s s' H' U₂ [.LG, .LG, .Sq] us U')
    (hall : AllFillableStrict R s s' H' U') :
    OneOverflatState U' s H' j₀ (h_th + 2) h ∨
      ∃ j_dp : Fin s, DeadTriggerState U' s H' j_dp j₀ h_th h := by sorry

end TetrisHard.Rows.Padded
