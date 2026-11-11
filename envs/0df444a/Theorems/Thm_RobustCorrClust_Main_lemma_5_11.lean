-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_5_11
-- name    : RobustCorrClust.Main.lemma_5_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:41:32.012459+00:00
-- url     : https://prove2.me/theorems/3c458e59-0db4-4b45-9c6e-0e9862af7b5f
-- title:
--   Lemma 5.11 — every minimizer y⋆ of φ satisfies −R ≤ 2 − R ≤ y⋆_u ≤ 1, so y⋆ ∈ B
-- statement:
--   Let $C$ be a weighted adjacency matrix, $R=n+\max_u\sum_vC_{uv}$ and $B=[-R,1]^n$. Every minimizer $y^\star$ of $\varphi$ over $\mathbb R^n$ satisfies
--   $$-R\le2-R\le y^\star_u\le1\qquad\text{for every }u,$$
--   and in particular $y^\star\in B$. This is what makes projected gradient descent on the box $B$ lose nothing.
--
--   Differences from the source:
--   - generalization: $C$ the weighted adjacency matrix of the rescaled sparsifier $\tilde H$ ("here and throughout Part B", p. 21) → $C$ any weighted adjacency matrix (symmetric, nonnegative, zero diagonal), the input class of Theorem 3; reason: Theorem 3 is stated for this general $C$ (p. 21) and the lemma is part of its proof; the paper's $\tilde H$ is such a matrix.
--   - encoding: minimizer of $\varphi$ over $\mathbb R^n$ → $\varphi(y^\star)\le\varphi(z)$ for every $z$; reason: definition of a minimizer.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 31, Lemma 5.11

import Mathlib
import Definitions.Def_RobustCorrClust_Main_NCMDual

namespace RobustCorrClust.Main

/-- Lemma 5.11 (p. 31): every minimizer `y⋆` of `φ` over `ℝⁿ` satisfies
`−R ≤ 2 − R ≤ y⋆_u ≤ 1` for every `u`; in particular `y⋆ ∈ B`. -/
theorem lemma_5_11 {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsWeightedGraph C)
    (ystar : Fin n → ℝ) (hmin : ∀ z : Fin n → ℝ, phi C ystar ≤ phi C z) :
    (∀ u, -boxR C ≤ 2 - boxR C ∧ 2 - boxR C ≤ ystar u ∧ ystar u ≤ 1) ∧ InBox C ystar := by sorry

end RobustCorrClust.Main
