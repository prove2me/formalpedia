-- Prove2me | Theorems.Thm_SelfishRouting_Linear_lemma_4_4
-- name    : SelfishRouting.Linear.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:02.794179+00:00
-- url     : https://prove2.me/theorems/a36e8784-1a41-4a66-91e9-f6e8b45a2a3a
-- title:
--   Lemma 4.4 — a flow feasible for $(1+\delta)r$ costs at least $C(f^*)+\delta\sum_i L^*_i(f^*)\,r_i$
-- statement:
--   Let every edge have a linear latency $\ell_e(x)=a_ex+b_e$ with $a_e,b_e\ge 0$, let the rates $r_i$ be positive and the route incidences $0/1$, and let $f^*$ be an optimal flow for the rates $r$. Let $L^*_i(f^*)=\min_{P\in\mathcal P_i}\ell^*_P(f^*)$ be the minimum marginal cost of increasing flow on an $s_i$-$t_i$ path with respect to $f^*$. Then for every $\delta>0$, every flow $f$ feasible for the rates $(1+\delta)r$ satisfies
--   $$C(f)\ \ge\ C(f^*)+\delta\sum_{i=1}^{k}L^*_i(f^*)\,r_i .$$
--
--   The per-unit cost of pushing additional traffic through the network is at least the current minimum marginal path cost; this is what bounds the cost of augmenting the optimal flow for $r/2$ to a flow for $r$ in Theorem 4.5.
--
--   **Formalization Note** The rates $(1+\delta)r$ are $i\mapsto(1+\delta)r_i$. $L^*_i$ is the minimum of the marginal path costs over the routes serving $i$ (see the definition item; the routes form a nonempty finite set because $r_i>0$ and $f^*$ is feasible). The hypothesis $\delta>0$ is kept as printed. Routes are $0/1$ incidence columns (a disclosed generalization).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 16, Lemma 4.4

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

namespace SelfishRouting.Linear

open KellyStochasticNetworks

/-- Lemma 4.4 (p. 16): with linear latencies, if `f*` is optimal for the rates `r` and
`δ > 0`, then every flow feasible for the rates `(1 + δ) r` has cost at least
`C(f*) + δ ∑ᵢ L*ᵢ(f*) rᵢ`. -/
theorem lemma_4_4 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (xstar : Fin R → ℝ) (hxstar : IsOptimalFlow A s (linLatency a b) rate xstar)
    (δ : ℝ) (hδ : 0 < δ)
    (y : Fin R → ℝ) (hy : y ∈ wardropFeasible s (fun i => (1 + δ) * rate i)) :
    SelfishRouting.Bicriteria.cost A (linLatency a b) xstar +
        δ * ∑ i, minMarginalPathCost A s a b xstar i * rate i ≤
      SelfishRouting.Bicriteria.cost A (linLatency a b) y := by sorry

end SelfishRouting.Linear
