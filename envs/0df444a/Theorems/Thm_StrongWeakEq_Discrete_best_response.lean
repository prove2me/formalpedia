-- Prove2me | Theorems.Thm_StrongWeakEq_Discrete_best_response
-- name    : StrongWeakEq.Discrete.best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:30.724372+00:00
-- url     : https://prove2.me/theorems/42b40bfc-2418-4616-b956-390613da0dda
-- title:
--   Proof of Theorem 5.1, p. 27 — Φ has nonempty closed convex values and is upper semicontinuous
-- statement:
--   Assume the standing assumptions of §5 ($\mathcal A_i\subseteq\mathfrak P$, $\kappa(t,i,\cdot)$ continuous on $\mathfrak P$, (5.2)) and the hypotheses of Theorem 5.1: every $\mathcal A_i$ is nonempty, convex and closed, and every $\kappa(0,i,\cdot)$ is concave on $\mathfrak P$. Let $\Phi(u)=\{w\in\mathcal A: w\in\arg\max_{u'\in\mathcal A}V(i,u'\otimes_1u)\ \forall i\in S\}$ be the best-response correspondence. Then:
--
--   1. for every $u\in\mathcal A$, the set $\Phi(u)$ is a nonempty, closed, convex subset of $\mathcal A$;
--   2. $\Phi$ is upper semicontinuous on $\mathcal A$: whenever $u^n\in\mathcal A$, $u\in\mathcal A$, $u^n\to u$, $w^n\in\Phi(u^n)$ and $w^n\to w$, then
--   $$w\in\Phi(u).$$
--
--   These are exactly the hypotheses of Kakutani's fixed-point theorem for $\Phi$ on the compact convex set $\mathcal A$, whose fixed points are the equilibria.
--
--   **Formalization Note** Convergence is in the product topology of `Matrix (Fin N) (Fin N) ℝ`; upper semicontinuity is stated sequentially, as on the page and as in Kakutani's paper. The page quantifies over $w^n,w\in\mathcal A$; here $w$ is arbitrary, and $w\in\mathcal A$ is part of the conclusion. Nonemptiness of each $\mathcal A_i$ is added (see Theorem 5.1). States are `Fin N`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 27, proof of Theorem 5.1 (Appendix B.1)

import Mathlib
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel
import Definitions.Def_StrongWeakEq_Discrete_BestResponse

namespace StrongWeakEq.Discrete

open Filter Topology

/-- Proof of Theorem 5.1, p. 27: under the hypotheses of Theorem 5.1, the best-response
correspondence `Φ` has nonempty, closed, convex values inside `𝒜`, and is upper semicontinuous on `𝒜`:
`uⁿ → u`, `wⁿ → w`, `wⁿ ∈ Φ(uⁿ)` imply `w ∈ Φ(u)`. -/
theorem best_response {N : ℕ} {A : Fin N → Set (Fin N → ℝ)} {κ : ℕ → Fin N → (Fin N → ℝ) → ℝ}
    (hS : DStanding A κ) (hne : ∀ i, (A i).Nonempty)
    (hconv : ∀ i, Convex ℝ (A i)) (hclosed : ∀ i, IsClosed (A i))
    (hconc : ∀ i, ConcaveOn ℝ (Simplex N) (κ 0 i)) :
    (∀ u ∈ DControls A,
      (dBestResponse A κ u).Nonempty ∧ IsClosed (dBestResponse A κ u) ∧
        Convex ℝ (dBestResponse A κ u) ∧ dBestResponse A κ u ⊆ DControls A) ∧
    (∀ (un wn : ℕ → Matrix (Fin N) (Fin N) ℝ) (u w : Matrix (Fin N) (Fin N) ℝ),
      (∀ n, un n ∈ DControls A) → u ∈ DControls A → Tendsto un atTop (𝓝 u) →
      (∀ n, wn n ∈ dBestResponse A κ (un n)) → Tendsto wn atTop (𝓝 w) →
      w ∈ dBestResponse A κ u) := by sorry

end StrongWeakEq.Discrete
