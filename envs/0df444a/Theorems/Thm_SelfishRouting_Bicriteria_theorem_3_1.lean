-- Prove2me | Theorems.Thm_SelfishRouting_Bicriteria_theorem_3_1
-- name    : SelfishRouting.Bicriteria.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:26.498622+00:00
-- url     : https://prove2.me/theorems/3e571773-338e-4fe1-9787-06ed80e86a8f
-- title:
--   Theorem 3.1 — a Nash flow costs no more than any flow feasible for twice the rates
-- statement:
--   Consider a multicommodity routing instance: a $0/1$ edge–route incidence matrix $A$, commodities $i = 1,\dots,k$ with rates $r_i > 0$, routes $\mathcal P_i$ serving commodity $i$, and edge latency functions $\ell_e$ that are nonnegative, nondecreasing and continuous on $[0,\infty)$. If $f$ is a flow at Nash equilibrium for the rates $r$ and $f^*$ is any flow feasible for the rates $2r$, then
--   $$
--   C(f) \le C(f^*).
--   $$
--
--   This is the main result of §3. No bound on the ratio between the cost of a Nash flow and that of an optimal flow holds for general continuous nondecreasing latencies, but this bicriteria bound does: selfish routing is no worse than optimal routing of twice as much traffic.
--
--   **Formalization Note.** The comparison is with every flow feasible for $2r$, as on the page; no optimality of $f^*$ is assumed. Routes are arbitrary $0/1$ incidence columns rather than simple paths in a graph (a generalization; the proof uses no graph structure). Latencies are assumed continuous rather than differentiable (footnote 3, p. 7, and §3, p. 11), and the hypotheses on $\ell_e$ concern $[0,\infty)$ only. Nash flows follow Definition 2.1 with $P_1 \ne P_2$ and $\delta > 0$.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 12, Theorem 3.1

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model

namespace SelfishRouting.Bicriteria

open KellyStochasticNetworks

/-- Theorem 3.1 (p. 12): the cost of a Nash flow for rates `r` is at most the cost of any
flow feasible for the rates `2r`. -/
theorem theorem_3_1 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (s : Fin R → Fin Sd)
    (ℓ : Fin J → ℝ → ℝ) (rate : Fin Sd → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hrate : ∀ i, 0 < rate i)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (x y : Fin R → ℝ) (hx : IsNashFlow A s ℓ rate x)
    (hy : y ∈ wardropFeasible s (fun i => 2 * rate i)) :
    cost A ℓ x ≤ cost A ℓ y := by sorry

end SelfishRouting.Bicriteria
