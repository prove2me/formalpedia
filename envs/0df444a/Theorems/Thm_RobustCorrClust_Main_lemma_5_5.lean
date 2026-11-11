-- Prove2me | Theorems.Thm_RobustCorrClust_Main_lemma_5_5
-- name    : RobustCorrClust.Main.lemma_5_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:41:39.105998+00:00
-- url     : https://prove2.me/theorems/2e75bed5-6c7c-4eb6-a414-6da7bbecf744
-- title:
--   Lemma 5.5 — φ is convex and differentiable with ∇φ(y) = diag(M(y)⁺) − 1, and ∇φ is 1-Lipschitz
-- statement:
--   Let $C$ be a weighted adjacency matrix and $\varphi(y)=\tfrac12\|M(y)^+\|_F^2-\mathbf 1^\top y$ on $\mathbb R^n$. Then $\varphi$ is convex and differentiable on $\mathbb R^n$ with
--   $$\nabla\varphi(y)=\mathrm{diag}(M(y)^+)-\mathbf 1,$$
--   and the gradient is $1$-Lipschitz: $\|\nabla\varphi(y')-\nabla\varphi(y)\|\le\|y'-y\|$ for all $y,y'\in\mathbb R^n$, in the Euclidean norm.
--
--   Differences from the source:
--   - generalization: $C$ the weighted adjacency matrix of the rescaled sparsifier $\tilde H$ ("here and throughout Part B", p. 21) → $C$ any weighted adjacency matrix (symmetric, nonnegative, zero diagonal), the input class of Theorem 3; reason: Theorem 3 is stated for this general $C$ (p. 21) and the lemma is part of its proof; the paper's $\tilde H$ is such a matrix.
--   - encoding: $\nabla\varphi(y)=\mathrm{diag}(M(y)^+)-\mathbf 1$ → $\varphi$ has a Fréchet derivative at $y$ given by $h\mapsto\sum_u\big((M(y)^+)_{uu}-1\big)h_u$; reason: the gradient for the Euclidean inner product.
--   - encoding: $\|\nabla\varphi(y')-\nabla\varphi(y)\|\le\|y'-y\|$ → the same inequality between squared Euclidean norms; reason: equivalent, both sides nonnegative.
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 27, Lemma 5.5

import Mathlib
import Definitions.Def_RobustCorrClust_Main_NCMDual

namespace RobustCorrClust.Main

/-- Lemma 5.5 (p. 27): `φ` is convex and differentiable on `ℝⁿ`, with gradient
`∇φ(y) = diag(M(y)⁺) − 1` (for the Euclidean inner product), and the gradient is 1-Lipschitz in
the Euclidean norm: `‖∇φ(y′) − ∇φ(y)‖ ≤ ‖y′ − y‖` (written with squared norms). -/
theorem lemma_5_5 {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsWeightedGraph C) :
    ConvexOn ℝ Set.univ (phi C) ∧
    (∀ y : Fin n → ℝ, ∃ L : (Fin n → ℝ) →L[ℝ] ℝ, HasFDerivAt (phi C) L y ∧
        ∀ h : Fin n → ℝ, L h = ∑ u, (posPart (Mmat C y) u u - 1) * h u) ∧
    (∀ y y' : Fin n → ℝ,
        ∑ u, ((posPart (Mmat C y') u u - 1) - (posPart (Mmat C y) u u - 1)) ^ 2 ≤
          ∑ u, (y' u - y u) ^ 2) := by sorry

end RobustCorrClust.Main
