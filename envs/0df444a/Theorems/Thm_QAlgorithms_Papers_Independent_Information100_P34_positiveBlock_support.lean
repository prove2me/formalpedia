-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P34_positiveBlock_support
-- name    : QAlgorithms.Papers.Independent.Information100.P34.positiveBlock_support
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:26:22.844813+00:00
-- url     : https://prove2.me/theorems/6f88c952-2923-4bce-a106-24ccdac5c27b
-- title:
--   Lemma 19: support containment of an off-diagonal positive block
-- statement:
--   Let $A\in\mathbb C^{n\times n}$, $B\in\mathbb C^{m\times m}$ and $C\in\mathbb C^{n\times m}$. Let $\Pi_A$ and $\Pi_B$ be the orthogonal projections onto their ranges. If the block matrix is positive semidefinite, then
--
--   $$\begin{pmatrix}A&C\\C^\dagger&B\end{pmatrix}\succeq0\quad\Longrightarrow\quad C=\Pi_A C\Pi_B.$$
--
--   No normalization or full-rank assumption is required. This identity locates the off-diagonal block inside the supports of its diagonal blocks.
-- source:
--   The Structure of Higher-Order Quantum Resources with an Application to Coherence, arXiv:2609.40186v1, PDF p. 30, Lemma 19

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- Lemma 19, Eq.(C42), PDF p.30: no rank or normalization premise. -/
theorem positiveBlock_support {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (C : Matrix (Fin n) (Fin m) ℂ)
    (h : (Matrix.fromBlocks A C Cᴴ B).PosSemidef) :
    C = supportProjector A * C * supportProjector B := by sorry

end QAlgorithms.Papers.Independent.Information100.P34

end
