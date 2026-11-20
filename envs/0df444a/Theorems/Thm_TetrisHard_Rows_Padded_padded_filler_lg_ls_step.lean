-- Prove2me | Theorems.Thm_TetrisHard_Rows_Padded_padded_filler_lg_ls_step
-- name    : TetrisHard.Rows.Padded.padded_filler_lg_ls_step
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-19T10:29:21.244982+00:00
-- url     : https://prove2.me/theorems/e725f15b-e8e1-4dbc-990b-f9892002cfe7
-- title:
--   Appendix C.2 — filler prefix [LG, LS] transition from one-overflat to trigger-happy
-- statement:
--   Let $R$ be a reasonable rotation model and let $s \le s'$ and $H' \ge 0$. Starting from a board $U$ in state $\mathrm{OneOverflatState}(U,s,H',j_0,h_0,\mathbf{h})$, every zero-waste bucket play of the two-piece filler prefix $[\mathrm{LG},\mathrm{LS}]$ that reaches an $\mathrm{AllFillableStrict}$ board $U_2$ must place both pieces in bucket $j_0$, advancing $j_0$ to a trigger-happy configuration at height $h_0+4$ while leaving every other bucket $k \ne j_0$ unprepped at height $h(k)$:
--   $$\mathrm{OneOverflatState}(U,s,H',j_0,h_0,\mathbf{h}) \;\Longrightarrow\; \mathrm{TriggerHappyAt}(U_2,j_0,H',h_0+4) \;\wedge\; \forall k \ne j_0,\ \mathrm{UnpreppedAt}(U_2,k,H',h(k)).$$
--
--   Any alternative placement of $[\mathrm{LG},\mathrm{LS}]$ into an unprepped bucket or a non-canonical overflat position produces an unfillable bucket by Propositions C.2, C.4, C.9, C.21-C.22, and C.24-C.27.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 5.3-5.4 (pp. 12-18), Section 6.2 (pp. 19-21), and Appendix C.1-C.2 (pp. 25-33), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_PaddedSoundness

namespace TetrisHard.Rows.Padded

theorem padded_filler_lg_ls_step
    (R : Rotation) (hReason : Reasonable R) (s s' H' : ℕ) (hs_le : s ≤ s')
    (U U₂ : Board) (us : List PieceState) (j₀ : Fin s) (h₀ : ℕ) (h : Fin s → ℕ)
    (hof : OneOverflatState U s H' j₀ h₀ h)
    (hp : NoRGSeqPlay R s s' H' U [.LG, .LS] us U₂)
    (hall : AllFillableStrict R s s' H' U₂) :
    TriggerHappyAt U₂ j₀.val H' (h₀ + 4) ∧ ∀ k : Fin s, k ≠ j₀ → UnpreppedAt U₂ k.val H' (h k) := by sorry

end TetrisHard.Rows.Padded
