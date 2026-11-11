-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_5_4
-- name    : RobustCorrClust.Main.lemma_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:41:41.144069+00:00
-- url     : https://prove2.me/theorems/69ca3be9-c332-462e-a90d-0e7bc20995a3
-- title:
--   Lemma 5.4 — closed form of the dual: d(y) is attained uniquely at M(y)⁺
-- statement:
--   Let $C$ be a weighted adjacency matrix (symmetric, nonnegative, zero diagonal), $M(y)=C+\mathrm{Diag}(y)$, $f(X)=\tfrac12\|X-C\|_F^2$ and $L(X,y)=f(X)-\sum_uy_u(X_{uu}-1)$. For every $y\in\mathbb R^n$, the minimum
--   $$d(y)=\min_{X\in S^n_+}L(X,y)$$
--   is attained at $M(y)^+$ and only there, and
--   $$d(y)=\tfrac12\|C\|_F^2-\Big(\tfrac12\|M(y)^+\|_F^2-\mathbf 1^\top y\Big).$$
--   This turns the $n$ diagonal constraints of the nearest-correlation-matrix problem into an unconstrained dual in $n$ variables.
--
--   Differences from the source:
--   - generalization: $C$ the weighted adjacency matrix of the rescaled sparsifier $\tilde H$ ("here and throughout Part B", p. 21) → $C$ any weighted adjacency matrix (symmetric, nonnegative, zero diagonal), the input class of Theorem 3; reason: Theorem 3 is stated for this general $C$ (p. 21) and the lemma is part of its proof; the paper's $\tilde H$ is such a matrix.
--   - encoding: "the minimum $d(y)$ is attained uniquely at $M(y)^+$ and $d(y)=\dots$" → four clauses: $M(y)^+$ is positive semidefinite, $L(M(y)^+,y)\le L(X,y)$ for every positive semidefinite $X$, any positive semidefinite $X$ with $L(X,y)\le L(M(y)^+,y)$ equals $M(y)^+$, and $L(M(y)^+,y)$ equals the formula; reason: states the attained minimum without a real infimum.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 25, Lemma 5.4

import Mathlib
import Definitions.Def_RobustCorrClust_Main_NCMDual

namespace RobustCorrClust.Main

/-- Lemma 5.4 (p. 25): for every `y ∈ ℝⁿ`, the minimum `d(y) = min_{X ∈ Sⁿ₊} L(X, y)` is attained
uniquely at `M(y)⁺`, and `d(y) = ½‖C‖²_F − (½‖M(y)⁺‖²_F − 1ᵀy)`. -/
theorem lemma_5_4 {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsWeightedGraph C)
    (y : Fin n → ℝ) :
    (posPart (Mmat C y)).PosSemidef ∧
    (∀ X : Matrix (Fin n) (Fin n) ℝ, X.PosSemidef →
        lagr C (posPart (Mmat C y)) y ≤ lagr C X y) ∧
    (∀ X : Matrix (Fin n) (Fin n) ℝ, X.PosSemidef →
        lagr C X y ≤ lagr C (posPart (Mmat C y)) y → X = posPart (Mmat C y)) ∧
    lagr C (posPart (Mmat C y)) y =
      frobSq C / 2 - (frobSq (posPart (Mmat C y)) / 2 - ∑ u, y u) := by sorry

end RobustCorrClust.Main
