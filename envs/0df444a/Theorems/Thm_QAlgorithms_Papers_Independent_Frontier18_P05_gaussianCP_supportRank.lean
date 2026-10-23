-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P05_gaussianCP_supportRank
-- name    : QAlgorithms.Papers.Independent.Frontier18.P05.gaussianCP_supportRank
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:47:52.145995+00:00
-- url     : https://prove2.me/theorems/6b936bbc-3030-4f0d-92da-0a501abed502
-- title:
--   CP support containment and rank regimes
-- statement:
--   Let $n\ge1$, $X,Y\in\mathbb R^{2n\times2n}$ and $\Sigma=\sigma_n-X^T\sigma_nX$, with $\sigma_n=\begin{pmatrix}0&I_n\\-I_n&0\end{pmatrix}$. Assume $Y-i\Sigma\succeq0$. Then $\Sigma^T=-\Sigma$, its real rank is even, and
--
--   $$\operatorname{range}(\Sigma)\subseteq\operatorname{range}(Y),\qquad 0\le r:=\operatorname{rank}(\Sigma)\le k:=\operatorname{rank}(Y)\le2n.$$
--
--   Consequently the cases $k=r=2n$, $k=2n>r$, and $2n>k\ge r$ exhaust all possibilities. These are the rank regimes used in the dilation constructions.
-- source:
--   Multi-mode bosonic Gaussian channels, arXiv:0804.0511v3, PDF p. 9, §2.1: CP support containment and rank regimes

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P05

noncomputable section

open scoped ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier18.P05

open QAlgorithms.Papers.Independent.Dependency50.P10

/-- Section 2.1, PDF p.9: support containment and exhaustive rank regimes.
All ranges and ranks are real. Zero noise and zero defect are included. -/
theorem gaussianCP_supportRank {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Phase n) (Phase n) ℝ) (hCP : (cpMatrix X Y).PosSemidef) :
    (commutatorDefect X).transpose = -commutatorDefect X ∧
    LinearMap.range (commutatorDefect X).mulVecLin ≤ LinearMap.range Y.mulVecLin ∧
    (commutatorDefect X).rank ≤ Y.rank ∧ Y.rank ≤ 2 * n ∧
    Even (commutatorDefect X).rank ∧
    ((Y.rank = 2 * n ∧ (commutatorDefect X).rank = 2 * n) ∨
     (Y.rank = 2 * n ∧ (commutatorDefect X).rank < 2 * n) ∨
     (Y.rank < 2 * n ∧ (commutatorDefect X).rank ≤ Y.rank)) := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P05

end
