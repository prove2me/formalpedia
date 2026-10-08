-- Prove2me | Theorems.Thm_WassDDRO_Extremal_theorem_4_4
-- name    : WassDDRO.Extremal.theorem_4_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:57:00.499393+00:00
-- url     : https://prove2.me/theorems/4a92c140-d524-4ca6-9c97-6bb695bcf4dc
-- title:
--   Theorem 4.4 (Worst-case distributions), p. 14 — under Assumption 4.1, (10) equals the value of (13), and near-optimal points of (13) give distributions attaining (10) asymptotically
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra, let $N, K \ge 1$, let $\Xi \subseteq E$ contain the samples $\hat\xi_1,\dots,\hat\xi_N$, let $\varepsilon \ge 0$, and let $\ell_1,\dots,\ell_K : E \to \overline{\mathbb R}$ be measurable with $\ell = \max_k \ell_k$. Suppose Assumption 4.1 holds: $\Xi$ is convex and closed, each $-\ell_k$ is proper, convex and lower semicontinuous, and no $\ell_k$ is identically $-\infty$ on $\Xi$. Then:
--
--   1. The worst-case expectation (10) equals the optimal value of the finite convex program (13):
--   $$\sup_{\mathbb Q\in\mathbb B_\varepsilon(\widehat{\mathbb P}_N)}\mathbb E^{\mathbb Q}[\ell(\xi)] \;=\; \sup_{\alpha_{ik},q_{ik}}\Big\{\frac1N\sum_{i=1}^N\sum_{k=1}^K\alpha_{ik}\ell_k\Big(\hat\xi_i-\frac{q_{ik}}{\alpha_{ik}}\Big) : \frac1N\sum_{i,k}\|q_{ik}\|\le\varepsilon,\ \sum_k\alpha_{ik}=1,\ \alpha_{ik}\ge0,\ \hat\xi_i-\frac{q_{ik}}{\alpha_{ik}}\in\Xi\Big\}.$$
--   2. Let $(\alpha_{ik}(r), q_{ik}(r))_{r\in\mathbb N}$ be feasible decisions of (13) whose objective values converge to the supremum of (13), and put $\xi_{ik}(r) = \hat\xi_i - q_{ik}(r)/\alpha_{ik}(r)$ and $\mathbb Q_r = \frac1N\sum_{i,k}\alpha_{ik}(r)\delta_{\xi_{ik}(r)}$. Then every $\mathbb Q_r$ lies in $\mathbb B_\varepsilon(\widehat{\mathbb P}_N)$, and
--   $$\sup_{\mathbb Q\in\mathbb B_\varepsilon(\widehat{\mathbb P}_N)}\mathbb E^{\mathbb Q}[\ell(\xi)] = \lim_{r\to\infty}\mathbb E^{\mathbb Q_r}[\ell(\xi)] = \lim_{r\to\infty}\frac1N\sum_{i=1}^N\sum_{k=1}^K\alpha_{ik}(r)\,\ell(\xi_{ik}(r)).$$
--
--   Fractions in (13) follow the paper's conventions: when $\alpha_{ik} = 0$ the constraint forces $q_{ik} = 0$ and the $ik$-th objective term is $0$.
--
--   The theorem shows that the worst case over a Wasserstein ball around the empirical distribution can be approached by discrete distributions with at most $NK$ atoms, computed from a finite convex program; this is what makes stress tests of a decision against its extremal distributions practical.
--
--   **Formalization Note** Values are in `EReal`, so the limits may be $+\infty$; no finiteness is assumed. The expectation is the extended expectation of p. 5. The printed second limit "$\lim_{k\to\infty}$" is read as $\lim_{r\to\infty}$ (the sequence index). The hypotheses $N, K \ge 1$, $\hat\xi_i \in \Xi$ and the measurability of each $\ell_k$ are the paper's standing assumptions (§2, p. 5 and p. 11).
-- source:
--   Mohajerin Esfahani & Kuhn, arXiv:1505.05116v3, Theorem 4.4, p. 14; proof pp. 15–17

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting

open MeasureTheory Filter Topology

namespace WassDDRO.Extremal

/-- Theorem 4.4 (Worst-case distributions), p. 14. Under Assumption 4.1 the worst-case
expectation (10) equals the optimal value of the finite convex program (13), for every ε ≥ 0;
and for every feasible sequence of (13) whose objective values converge to the supremum of (13),
the discrete distributions Q_r lie in the Wasserstein ball and attain (10) asymptotically. The
printed second limit index "k → ∞" is the sequence index r. -/
theorem theorem_4_4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {K N : ℕ} (hK : 0 < K) (hN : 0 < N) (Ξ : Set E) (ℓ : Fin K → E → EReal)
    (hmeas : ∀ k, Measurable (ℓ k)) (ξhat : Fin N → E) (hξ : ∀ i, ξhat i ∈ Ξ)
    (ε : ℝ) (hε : 0 ≤ ε) (hA : Assumption41 Ξ ℓ) :
    worstCaseExpectation ε Ξ ξhat (maxLoss ℓ) = program13Value ε Ξ ξhat ℓ ∧
    ∀ (α : ℕ → Fin N → Fin K → ℝ) (q : ℕ → Fin N → Fin K → E),
      (∀ r, Feasible13 ε Ξ ξhat (α r) (q r)) →
      Tendsto (fun r => objective13 ξhat ℓ (α r) (q r)) atTop
        (𝓝 (program13Value ε Ξ ξhat ℓ)) →
      (∀ r, discreteQ ξhat (α r) (q r) ∈ WassersteinDRO.Duality.ambiguitySet ε 1 Ξ
          (WassersteinDRO.Duality.empiricalDistribution ξhat)) ∧
      Tendsto (fun r => DupacovaWets.Consistency.expect (discreteQ ξhat (α r) (q r)) (maxLoss ℓ)) atTop
        (𝓝 (worstCaseExpectation ε Ξ ξhat (maxLoss ℓ))) ∧
      Tendsto (fun r => ((1 / (N : ℝ) : ℝ) : EReal) *
          ∑ i, ∑ k, term13 (maxLoss ℓ) (ξhat i) (α r i k) (q r i k)) atTop
        (𝓝 (worstCaseExpectation ε Ξ ξhat (maxLoss ℓ))) := by sorry

end WassDDRO.Extremal
