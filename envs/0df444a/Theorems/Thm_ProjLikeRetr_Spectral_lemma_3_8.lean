-- Prove2me | Theorems.Thm_ProjLikeRetr_Spectral_lemma_3_8
-- name    : ProjLikeRetr.Spectral.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:02:07.893821+00:00
-- url     : https://prove2.me/theorems/c554a4bc-8a86-407c-9e6e-2565bea64e38
-- title:
--   Lemma 3.8, p. 13 — near a sorted $\bar x$, $\max x^\top P y$ over permutations fixing $\bar x$ is attained with $Py$ sorted
-- statement:
--   Let $\bar x \in \mathbb R^n_\downarrow$. Then there is $\delta_1 > 0$ such that for every $\delta \in (0, \delta_1]$ the following holds. For any $y \in B(\bar x, \delta)$ and $x \in \mathbb R^n_\downarrow \cap B(\bar x, \delta)$, the maximum of the inner product
--   $$
--   \max_{P \in \mathbf \Sigma_n,\ P\bar x = \bar x} x^\top P y
--   $$
--   over the permutations that fix $\bar x$ is attained at a permutation $P$ with $Py \in \mathbb R^n_\downarrow$: there is $P \in \mathbf \Sigma_n$ with $P \bar x = \bar x$ and $P y \in \mathbb R^n_\downarrow$ such that $x^\top Q y \le x^\top P y$ for every $Q \in \mathbf \Sigma_n$ with $Q \bar x = \bar x$.
--
--   Here $B(\bar x, \delta)$ is the open Euclidean ball. The lemma is the rearrangement step that lets the proof of Theorem 3.9 restrict the projection onto $\mathcal M$ to sorted points, (3.20).
--
--   **Formalization Note** "For all $\delta > 0$ small enough" is rendered as $\exists \delta_1 > 0,\ \forall \delta \in (0, \delta_1]$. "The maximum is attained when $Py \in \mathbb R^n_\downarrow$" is rendered as the existence of a maximizing permutation that fixes $\bar x$ and sorts $y$. Permutations act by `permAct`.
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 13, Lemma 3.8 (proof pp. 13–14, (3.17))

import Mathlib
import Definitions.Def_ProjLikeRetr_Spectral_SpectralSet

namespace ProjLikeRetr.Spectral

/-- Lemma 3.8, p. 13: for all small enough `δ > 0`, for `y ∈ B(x̄, δ)` and
`x ∈ ℝⁿ↓ ∩ B(x̄, δ)`, the maximum of `xᵀPy` over the permutations fixing `x̄` is attained
at a permutation `P` with `Py ∈ ℝⁿ↓`. -/
theorem lemma_3_8 {n : ℕ} (xbar : EuclideanSpace ℝ (Fin n)) (hxbar : xbar ∈ sortedDesc n) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∀ y x : EuclideanSpace ℝ (Fin n), y ∈ Metric.ball xbar δ → x ∈ sortedDesc n →
        x ∈ Metric.ball xbar δ →
        ∃ σ : Equiv.Perm (Fin n), permAct σ xbar = xbar ∧ permAct σ y ∈ sortedDesc n ∧
          ∀ τ : Equiv.Perm (Fin n), permAct τ xbar = xbar →
            inner ℝ x (permAct τ y) ≤ inner ℝ x (permAct σ y) := by sorry

end ProjLikeRetr.Spectral
