-- Prove2me | Theorems.Thm_SelfishRouting_Splittable_nash_optimal_bar
-- name    : SelfishRouting.Splittable.nash_optimal_bar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:22.677013+00:00
-- url     : https://prove2.me/theorems/f7fa802b-2024-4653-8763-fd1993e8a121
-- title:
--   Proof of Theorem 5.4, p. 20 — a finite splittable Nash flow is optimal for $(G, r, \bar\ell)$
-- statement:
--   Consider a finite splittable instance $(G,r,\ell)$ with $k$ agents of rates $r_i>0$, whose latency functions $\ell_e$ are nonnegative, nondecreasing and continuous on $[0,\infty)$ and such that $x\cdot\ell_e(x)$ is convex on $[0,\infty)$ for every edge $e$. Let $f$ be a flow at Nash equilibrium, and let $\bar\ell$ be the modified latency functions built from the edge flows of $f$. Then $f$ is optimal for the instance $(G,r,\bar\ell)$: for every flow $g$ feasible for the rates $r$,
--
--   $$\sum_P \bar\ell_P(f)\,f_P\;\le\;\sum_P\bar\ell_P(g)\,g_P .$$
--
--   This is the central claim of the proof of Theorem 5.4. It is where the finite splittable model departs from the nonatomic proof of Theorem 3.1: the equilibrium is used through each agent's total cost $C_i$, and the convexity of $x\cdot\ell_e(x)$ makes $(G,r,\bar\ell)$ a convex program.
--
--   **Formalization Note** "Optimal for the instance $(G,r,\bar\ell)$" is rendered as minimality of the $\bar\ell$-cost over all flows feasible for the rates $r$; a finite splittable flow and a flow of §2 have the same feasible set in this encoding. Routes are $0/1$ incidence columns (a generalization of simple paths); continuity replaces differentiability (footnote 3, p. 7); all hypotheses on $\ell_e$ are on $[0,\infty)$.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 20, proof of Theorem 5.4, second paragraph, first sentence

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Splittable_Model
import Definitions.Def_SelfishRouting_Bicriteria_BarLatency

namespace SelfishRouting.Splittable

open KellyStochasticNetworks

theorem nash_optimal_bar {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (ℓ : Fin J → ℝ → ℝ) (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (hℓmono : ∀ j, MonotoneOn (ℓ j) (Set.Ici 0))
    (hℓcont : ∀ j, ContinuousOn (ℓ j) (Set.Ici 0))
    (hconv : ∀ j, ConvexOn ℝ (Set.Ici 0) (fun t => t * ℓ j t))
    (x : Fin R → ℝ) (hx : IsSplittableNash A s ℓ rate x) :
    ∀ z ∈ wardropFeasible s rate,
      SelfishRouting.Bicriteria.cost A (SelfishRouting.Bicriteria.barLatency ℓ (linkFlow A x)) x ≤ SelfishRouting.Bicriteria.cost A (SelfishRouting.Bicriteria.barLatency ℓ (linkFlow A x)) z := by sorry

end SelfishRouting.Splittable
