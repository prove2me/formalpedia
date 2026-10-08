-- Prove2me | Theorems.Thm_SelfishRouting_Splittable_two_rate_bar_lower_bound
-- name    : SelfishRouting.Splittable.two_rate_bar_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:31.544404+00:00
-- url     : https://prove2.me/theorems/6e74cfc7-1fba-4cba-baab-531c1ef6197f
-- title:
--   Proof of Theorem 5.4, p. 20 — every flow feasible for $(G, 2r, \bar\ell)$ has $\bar\ell$-cost at least $2C(f)$
-- statement:
--   Consider a finite splittable instance $(G,r,\ell)$ with $k$ agents of rates $r_i>0$, whose latency functions $\ell_e$ are nonnegative, nondecreasing and continuous on $[0,\infty)$ and such that $x\cdot\ell_e(x)$ is convex on $[0,\infty)$ for every edge $e$. Let $f$ be a flow at Nash equilibrium and $\bar\ell$ the modified latency functions built from the edge flows of $f$. Then every flow $g$ feasible for the doubled rates $2r$ (each agent $i$ sends $2r_i$) satisfies
--
--   $$\sum_P \bar\ell_P(g)\,g_P\;\ge\;2\,C(f).$$
--
--   Combined with the bound $\sum_P\bar\ell_P(f^*)f^*_P - C(f^*)\le C(f)$ it gives $C(f^*)\ge C(f)$, which is Theorem 5.4.
--
--   **Formalization Note** The right-hand side is $2C(f)$ with $C$ the cost under the original latencies, as printed; the $\bar\ell$-cost of $f$ equals $C(f)$ because $\bar\ell_e(f_e)=\ell_e(f_e)$. Routes are $0/1$ incidence columns (a generalization of simple paths); continuity replaces differentiability; all hypotheses on $\ell_e$ are on $[0,\infty)$.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 20, proof of Theorem 5.4, last paragraph

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Splittable_Model
import Definitions.Def_SelfishRouting_Bicriteria_BarLatency

namespace SelfishRouting.Splittable

open KellyStochasticNetworks

theorem two_rate_bar_lower_bound {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (ℓ : Fin J → ℝ → ℝ) (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (hconv : ∀ j, ConvexOn ℝ (Set.Ici 0) (fun t => t * ℓ j t))
    (x : Fin R → ℝ) (hx : IsSplittableNash A s ℓ rate x) :
    ∀ z ∈ wardropFeasible s (fun i => 2 * rate i),
      2 * SelfishRouting.Bicriteria.cost A ℓ x ≤ SelfishRouting.Bicriteria.cost A (SelfishRouting.Bicriteria.barLatency ℓ (linkFlow A x)) z := by sorry

end SelfishRouting.Splittable
