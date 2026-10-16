-- Prove2me | Theorems.Thm_SubsetShrink_LowerBound_maurey_approximation
-- name    : SubsetShrink.LowerBound.maurey_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:36.206192+00:00
-- url     : https://prove2.me/theorems/4d2fcab2-0fb1-4f86-8d22-d72cd09c6553
-- title:
--   Proof of Theorem 4 (B.9), p. 44 — Maurey: some β̃ ∈ B0(k/2) has ‖Xβ* − Xβ̃‖² ≤ 2‖β*‖₁²/k
-- statement:
--   Let $X$ be a real $n\times p$ matrix whose columns have unit Euclidean norm, let $k\ge1$ be an integer and let $\beta^*\in\mathbb R^p$ be arbitrary. Then there is a vector $\tilde\beta^*\in\mathbb R^p$ with $\|\tilde\beta^*\|_0\le k/2$ such that
--   $$
--   \|X\beta^*-X\tilde\beta^*\|^2\le\frac{2\|\beta^*\|_1^2}{k}.
--   $$
--
--   This is the approximation step of the proof of Theorem 4, which the paper attributes to Maurey's empirical method: a vector of $\ell_1$ norm $\|\beta^*\|_1$ can be replaced by one with half the sparsity budget at a prediction cost of order $\|\beta^*\|_1^2/k$.
--
--   **Formalization Note** $\|\tilde\beta^*\|_0\le k/2$ is a comparison of real numbers, so for odd $k$ it means $\|\tilde\beta^*\|_0\le\lfloor k/2\rfloor$; the bound is true for every $k\ge1$ (for $k=1$ take $\tilde\beta^*=0$). No sparsity of $\beta^*$ and no relation between $k$ and $p$ is assumed.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 44, proof of Theorem 4 (B.9), the sentence citing Maurey's argument [49] and Lemma A.1 in [52]

import Mathlib
import Definitions.Def_SubsetShrink_LowerBound_Model

namespace SubsetShrink.LowerBound

/-- Proof of Theorem 4, p. 44 (Maurey's argument, Lemma A.1 in [52]): for unit-norm columns and every
`β*`, there is `β̃*` with `‖β̃*‖₀ ≤ k/2` (real comparison) and `‖Xβ* − Xβ̃*‖² ≤ 2‖β*‖₁²/k`. -/
theorem maurey_approximation {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (k : ℕ)
    (βstar : Fin p → ℝ) (hX : SubsetShrink.Events.UnitCols X) (hk : 1 ≤ k) :
    ∃ βt : Fin p → ℝ, (l0 βt : ℝ) ≤ (k : ℝ) / 2 ∧
      ∑ i, (X.mulVec βstar i - X.mulVec βt i) ^ 2 ≤ 2 * SubsetShrink.Events.l1 βstar ^ 2 / k := by sorry

end SubsetShrink.LowerBound
