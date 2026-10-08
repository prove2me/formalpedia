-- Prove2me | Theorems.Thm_SelfishRouting_Splittable_theorem_5_4
-- name    : SelfishRouting.Splittable.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:13.804977+00:00
-- url     : https://prove2.me/theorems/4fcce07a-3bf5-402d-9981-81ad0479da6f
-- title:
--   Theorem 5.4 — a finite splittable Nash flow costs no more than any flow feasible for twice the rates
-- statement:
--   Consider a **finite splittable instance** $(G,r,\ell)$: a network with $k$ agents, agent $i$ sending $r_i>0$ units of flow over its own set of paths $\mathcal P_i$ and free to split it among them. The latency functions $\ell_e$ are nonnegative, nondecreasing and continuous on $[0,\infty)$, and $x\cdot\ell_e(x)$ is convex on $[0,\infty)$ for each edge $e$. Let $f$ be a flow at **Nash equilibrium**: for each agent $i$, $f^{(i)}$ minimizes the agent's total latency $C_i(f)=\sum_{P\in\mathcal P_i}\ell_P(f)f^{(i)}_P$ given the flows $f^{(j)}$, $j\ne i$, of the other agents. If $f^*$ is feasible for the finite splittable instance $(G,2r,\ell)$, in which every agent sends twice its rate, then
--
--   $$C(f)\le C(f^*),$$
--
--   where $C(f)=\sum_P\ell_P(f)f_P$ is the total latency.
--
--   The theorem is the finite-agent analogue of the bicriteria Theorem 3.1: selfish routing by finitely many agents who control non-negligible amounts of traffic costs no more than an optimal routing of twice the traffic. Theorem 3.1 is its limiting case as the number of agents tends to infinity.
--
--   **Formalization Note** Paths are encoded as $0/1$ incidence columns (`A`) with an owner map `s`, so the statement holds for every family of routes, of which the paper's simple-path families are one instance; agents with identical source–destination pairs get separate route copies. Continuity on $[0,\infty)$ replaces differentiability, as footnote 3 (p. 7) and §5.2 ("continuous nondecreasing latency functions") allow. The existence of a Nash flow (Rosen) is not assumed or claimed; the theorem quantifies over Nash flows. Feasibility for $(G,2r,\ell)$ is `wardropFeasible s (fun i => 2 * rate i)`.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 20, Theorem 5.4

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Splittable_Model
import Definitions.Def_SelfishRouting_Bicriteria_BarLatency

namespace SelfishRouting.Splittable

open KellyStochasticNetworks

theorem theorem_5_4 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (ℓ : Fin J → ℝ → ℝ) (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (hconv : ∀ j, ConvexOn ℝ (Set.Ici 0) (fun t => t * ℓ j t))
    (x : Fin R → ℝ) (hx : IsSplittableNash A s ℓ rate x)
    (y : Fin R → ℝ) (hy : y ∈ wardropFeasible s (fun i => 2 * rate i)) :
    SelfishRouting.Bicriteria.cost A ℓ x ≤ SelfishRouting.Bicriteria.cost A ℓ y := by sorry

end SelfishRouting.Splittable
