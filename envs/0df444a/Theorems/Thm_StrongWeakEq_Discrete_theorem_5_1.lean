-- Prove2me | Theorems.Thm_StrongWeakEq_Discrete_theorem_5_1
-- name    : StrongWeakEq.Discrete.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:38:57.983464+00:00
-- url     : https://prove2.me/theorems/9e1645dd-c72f-42fe-a471-11fa46f895b1
-- title:
--   Theorem 5.1, p. 16 — an equilibrium exists when every 𝒜ᵢ is closed and convex and κ(0, i, ·) is concave
-- statement:
--   Consider the discrete-time model of §5: a Markov chain on $S=\{1,\dots,N\}$ whose transition matrix $u$ is chosen from $\mathcal A=\{u:u_i\in\mathcal A_i\ \forall i\}$ with $\mathcal A_i\subseteq\mathfrak P$, the probability simplex, and a payoff $\kappa(t,i,\alpha)$ that is continuous in $\alpha\in\mathfrak P$ and satisfies the summability condition (5.2), $\sum_{t\ge0}\sup_{(i,\alpha)}|\kappa(t,i,\alpha)|<\infty$. Suppose that for every $i\in S$:
--
--   1. $\mathcal A_i$ is nonempty, convex and closed;
--   2. $\kappa(0,i,\cdot)$ is concave on $\mathfrak P$.
--
--   Then there exists an **equilibrium**: some $u^*\in\mathcal A$ with
--   $$V(i,u^*)\ \ge\ V(i,u\otimes_1u^*)\qquad\text{for all }(i,u)\in S\times\mathcal A.$$
--
--   The result is an existence theorem for time-inconsistent control on an infinite horizon in discrete time, where backward induction is unavailable. Since $\mathfrak P$ is compact, no compactness assumption on $\mathcal A_i$ is needed beyond closedness.
--
--   **Formalization Note** Nonemptiness of each $\mathcal A_i$ is added: the page's hypotheses allow $\mathcal A_i=\emptyset$, where $\mathcal A$ is empty and no equilibrium exists. $V$ and $V(i,u\otimes_1u^*)$ are written through the marginals $(u^t)_{ij}$ of the chain as `tsum`s; (5.2) makes them convergent, and no summability is assumed. States are `Fin N`; at $N=0$ the nonemptiness hypothesis cannot hold, which is outside the paper's setting. Concavity is on the whole simplex, as on the page.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 16, Theorem 5.1 (proof Appendix B.1, p. 27)

import Mathlib
import Definitions.Def_StrongWeakEq_Discrete_DiscreteModel

namespace StrongWeakEq.Discrete

/-- Theorem 5.1, p. 16: if every `𝒜ᵢ` is convex and closed (and nonempty, an addition: with `𝒜ᵢ = ∅` the
set `𝒜` is empty), and `κ(0,i,·)` is concave on `𝔓` for every `i`, then an equilibrium exists. -/
theorem theorem_5_1 {N : ℕ} {A : Fin N → Set (Fin N → ℝ)} {κ : ℕ → Fin N → (Fin N → ℝ) → ℝ}
    (hS : DStanding A κ) (hne : ∀ i, (A i).Nonempty)
    (hconv : ∀ i, Convex ℝ (A i)) (hclosed : ∀ i, IsClosed (A i))
    (hconc : ∀ i, ConcaveOn ℝ (Simplex N) (κ 0 i)) :
    ∃ us, IsDEquilibrium A κ us := by sorry

end StrongWeakEq.Discrete
