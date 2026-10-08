-- Prove2me | Theorems.Thm_WassDDRO_Consistency_lemma_A_1
-- name    : WassDDRO.Consistency.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:15.564583+00:00
-- url     : https://prove2.me/theorems/4f976e57-759f-442f-8bb8-271f94163ad8
-- title:
--   Lemma A.1, p. 39 — an upper semicontinuous h with h(ξ) ≤ L(1+‖ξ‖) is the pointwise limit of non-increasing Lipschitz functions
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $\Xi\subseteq E$, and let $h:\Xi\to\mathbb R$ be upper semicontinuous (relative to $\Xi$). Suppose there is $L\ge0$ with
--   $$
--   h(\xi)\le L(1+\|\xi\|)\qquad\text{for all }\xi\in\Xi .
--   $$
--   Then there is a sequence of functions $h_k:\Xi\to\mathbb R$, $k\in\mathbb N$, such that
--
--   1. each $h_k$ is Lipschitz continuous on $\Xi$ (with some constant $L_k\ge0$);
--   2. the sequence is non-increasing: $h_{k+1}(\xi)\le h_k(\xi)$ for all $\xi\in\Xi$ and $k$;
--   3. $h_k(\xi)\to h(\xi)$ as $k\to\infty$ for every $\xi\in\Xi$.
--
--   This approximation lets one pass from the Kantorovich–Rubinstein duality, which controls expectations of Lipschitz functions, to expectations of a merely upper semicontinuous loss with linear growth; it is used in the proof of Theorem 3.6.
--
--   **Formalization Note** $h$ and the $h_k$ are functions on all of $E$ whose values outside $\Xi$ are ignored; Lipschitz continuity, monotonicity, convergence and the growth bound are all required only on $\Xi$.
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, Appendix A, Lemma A.1, p. 39; proof pp. 39–40

import Mathlib

open Filter Topology

namespace WassDDRO.Consistency

/-- Lemma A.1, p. 39. If `h : Ξ → ℝ` is upper semicontinuous and `h(ξ) ≤ L(1 + ‖ξ‖)` for some
`L ≥ 0`, there is a non-increasing sequence of Lipschitz continuous functions `h_k` on `Ξ`
converging pointwise to `h` on `Ξ`. Values of `h` and `h_k` off `Ξ` play no role. -/
theorem lemma_A_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Ξ : Set E) (h : E → ℝ) (husc : UpperSemicontinuousOn h Ξ) (L : ℝ) (hL : 0 ≤ L)
    (hgrowth : ∀ ξ ∈ Ξ, h ξ ≤ L * (1 + ‖ξ‖)) :
    ∃ hk : ℕ → E → ℝ, (∀ k, ∃ Lk : NNReal, LipschitzOnWith Lk (hk k) Ξ) ∧
      (∀ k, ∀ ξ ∈ Ξ, hk (k + 1) ξ ≤ hk k ξ) ∧
      ∀ ξ ∈ Ξ, Tendsto (fun k => hk k ξ) atTop (𝓝 (h ξ)) := by sorry

end WassDDRO.Consistency
