-- Prove2me | Theorems.Thm_TetrisHard_Rows_Padded_padded_initiator_and_terminator_step
-- name    : TetrisHard.Rows.Padded.padded_initiator_and_terminator_step
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:28:44.557181+00:00
-- url     : https://prove2.me/theorems/c8ca2dfe-7be7-4884-acb7-a0c7c8fbb236
-- title:
--   Appendix C.2 — multi-bucket initiator and terminator state transitions
-- statement:
--   Let $R$ be a reasonable rotation model and let $s \le s'$ and $H' \ge 0$. Under strictly fillable zero-waste bucket play:
--   1. **Initiator transition.** Starting from a board $U$ in state $\mathrm{AllUnpreppedHeights}(U,s,H',\mathbf{h})$, any play of $\mathrm{initiator} = [\mathrm{I},\mathrm{LG},\mathrm{Sq}]$ reaching an $\mathrm{AllFillableStrict}$ board $U'$ places all three pieces into a single bucket $j_0 < s$ and transitions to an overflat state of height $h(j_0)+2$:
--   $$\mathrm{AllUnpreppedHeights}(U,s,H',\mathbf{h}) \;\Longrightarrow\; \exists\, j_0 < s,\ \mathrm{OneOverflatState}(U',s,H',j_0,h(j_0)+2,\mathbf{h}).$$
--   2. **Terminator transition.** Starting from $\mathrm{OneOverflatState}(U,s,H',j_0,h_0,\mathbf{h})$, any play of $\mathrm{terminator} = [\mathrm{Sq},\mathrm{Sq}]$ reaching an $\mathrm{AllFillableStrict}$ board $U'$ places both squares in bucket $j_0$ and restores all buckets to unprepped state with $h(j_0)$ replaced by $h_0+4$:
--   $$\mathrm{OneOverflatState}(U,s,H',j_0,h_0,\mathbf{h}) \;\Longrightarrow\; \mathrm{AllUnpreppedHeights}(U',s,H',\mathbf{h}[j_0 \mapsto h_0+4]).$$
--
--   This formalizes the initiator and terminator transitions of Appendix C.2 via Propositions C.1-C.8, C.17-C.18, C.20, and C.23.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 5.3-5.4 (pp. 12-18), Section 6.2 (pp. 19-21), and Appendix C.1-C.2 (pp. 25-33), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_PaddedSoundness

namespace TetrisHard.Rows.Padded

theorem padded_initiator_and_terminator_step
    (R : Rotation) (hReason : Reasonable R) (s s' H' : ℕ) (hs_le : s ≤ s') :
    (∀ (U U' : Board) (us : List PieceState) (h : Fin s → ℕ),
      AllUnpreppedHeights U s H' h →
      NoRGSeqPlay R s s' H' U initiator us U' →
      AllFillableStrict R s s' H' U' →
      ∃ j₀ : Fin s, OneOverflatState U' s H' j₀ (h j₀ + 2) h) ∧
    (∀ (U U' : Board) (us : List PieceState) (j₀ : Fin s) (h₀ : ℕ) (h : Fin s → ℕ),
      OneOverflatState U s H' j₀ h₀ h →
      NoRGSeqPlay R s s' H' U terminator us U' →
      AllFillableStrict R s s' H' U' →
      AllUnpreppedHeights U' s H' (Function.update h j₀ (h₀ + 4))) := by sorry

end TetrisHard.Rows.Padded
