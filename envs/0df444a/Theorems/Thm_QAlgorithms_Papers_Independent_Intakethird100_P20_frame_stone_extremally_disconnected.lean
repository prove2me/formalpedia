-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P20_frame_stone_extremally_disconnected
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P20.frame_stone_extremally_disconnected
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:40:21.679511+00:00
-- url     : https://prove2.me/theorems/ac2d7a8b-152f-464a-9317-0e63acbaa962
-- title:
--   Proposition 3.7
-- statement:
--   Let $L$ be a complete lattice satisfying the frame law $a\wedge\bigvee S=\bigvee_{b\in S}(a\wedge b)$. Then its Stone spectrum is extremally disconnected, and
--
--   $$\overline{\bigcup_{a\in S}Q_a(L)}=Q_{\bigvee S}(L)\qquad(S\subseteq L).$$
--
--   Thus the closure of every open subset of the spectrum is open. The frame law is the source's meaning of complete distributivity, not the stronger modern two-index law.
-- source:
--   Observables I: Stone Spectra, arXiv:math-ph/0509020v1, PDF p. 45, Proposition 3.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P20

open Set TopologicalSpace

open QAlgorithms.Papers.Independent.Next46.P33 (Projection)

open scoped Topology

universe u v

/-- Proposition 3.7; de Groote, Observables I, PDF p./pp. 45.
-/
theorem frame_stone_extremally_disconnected {L : Type u} [CompleteLattice L] (hframe : HasFrameLaw L) :
    ExtremallyDisconnected (StoneSpectrum L) ∧
      ∀ s : Set L, closure (⋃ a ∈ s, stoneBasic a) = stoneBasic (sSup s) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P20

end
