-- Prove2me | Theorems.Thm_TetrisHard_Rows_Padded_padded_dead_trigger_eliminator
-- name    : TetrisHard.Rows.Padded.padded_dead_trigger_eliminator
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:28:32.16553+00:00
-- url     : https://prove2.me/theorems/c14c4fd7-3e76-4031-a954-b581a28ada43
-- title:
--   Appendix C.2 — elimination of simultaneous dead-plateau and trigger-happy configurations
-- statement:
--   Let $R$ be a reasonable rotation model and let $s \le s'$ and $H' \ge 0$. From any board $U$ in $\mathrm{DeadTriggerState}(U,s,H',j_{\mathrm{dp}},j_{\mathrm{th}},h_{\mathrm{th}},\mathbf{h})$ (containing a dead plateau in bucket $j_{\mathrm{dp}}$, a trigger-happy configuration in bucket $j_{\mathrm{th}} \ne j_{\mathrm{dp}}$, and unprepped configurations in all remaining buckets), neither a terminator prefix $[\mathrm{Sq},\mathrm{Sq}]$ nor a subsequent filler prefix $[\mathrm{LG},\mathrm{LS}]$ admits a zero-waste bucket play to an $\mathrm{AllFillableStrict}$ board:
--   $$\mathrm{DeadTriggerState}(U,s,H',j_{\mathrm{dp}},j_{\mathrm{th}},h_{\mathrm{th}},\mathbf{h}) \;\Longrightarrow\; \neg \exists\, U',\ \mathrm{NoRGSeqPlay}_R(s,s',H',U,[\mathrm{Sq},\mathrm{Sq}]\mathbin{+\!\!+}T,\mathbf{u},U') \wedge \mathrm{AllFillableStrict}_R(s,s',H',U'),$$
--   and analogously for $[\mathrm{LG},\mathrm{LS}]\mathbin{+\!\!+}T$.
--
--   Consequently, the dead-plateau branch of a filler block can never survive the next two pieces of `integerBlock`, forcing every filler block in a valid Phase-1 play to remain in the active bucket $j_0$.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 5.3-5.4 (pp. 12-18), Section 6.2 (pp. 19-21), and Appendix C.1-C.2 (pp. 25-33), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_PaddedSoundness

namespace TetrisHard.Rows.Padded

theorem padded_dead_trigger_eliminator
    (R : Rotation) (hReason : Reasonable R) (s s' H' : ℕ) (hs_le : s ≤ s') :
    (∀ (U U' : Board) (ts_tail : List Piece) (us : List PieceState)
       (j_dp j_th : Fin s) (h_th : ℕ) (h : Fin s → ℕ),
      DeadTriggerState U s H' j_dp j_th h_th h →
      NoRGSeqPlay R s s' H' U (.Sq :: .Sq :: ts_tail) us U' →
      AllFillableStrict R s s' H' U' → False) ∧
    (∀ (U U' : Board) (ts_tail : List Piece) (us : List PieceState)
       (j_dp j_th : Fin s) (h_th : ℕ) (h : Fin s → ℕ),
      DeadTriggerState U s H' j_dp j_th h_th h →
      NoRGSeqPlay R s s' H' U (.LG :: .LS :: ts_tail) us U' →
      AllFillableStrict R s s' H' U' → False) := by sorry

end TetrisHard.Rows.Padded
