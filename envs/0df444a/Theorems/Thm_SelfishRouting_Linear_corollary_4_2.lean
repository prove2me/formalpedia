-- Prove2me | Theorems.Thm_SelfishRouting_Linear_corollary_4_2
-- name    : SelfishRouting.Linear.corollary_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:00.293914+00:00
-- url     : https://prove2.me/theorems/117eab7b-b41c-4998-bc06-f01068bd8c2a
-- title:
--   Corollary 4.2 — with latencies $\ell_e(x)=a_ex$, a feasible flow is optimal iff it is at Nash equilibrium
-- statement:
--   Let every edge latency be proportional to its congestion, $\ell_e(x)=a_ex$ with $a_e\ge 0$, let the rates $r_i$ be positive and the route incidences $0/1$. Then for every flow $f$ feasible for the rates $r$,
--   $$f\ \text{is optimal}\iff f\ \text{is at Nash equilibrium}.$$
--
--   In such networks selfish routing loses nothing: the price of anarchy is exactly $1$.
--
--   **Formalization Note** The latencies are the linear latencies with $b_e=0$. "For any rate vector $r$" is the universal quantification over positive rates. Routes are $0/1$ incidence columns (a disclosed generalization).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 15, Corollary 4.2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

namespace SelfishRouting.Linear

open KellyStochasticNetworks

/-- Corollary 4.2 (p. 15): if every latency is `ℓ_e(x) = a_e x`, then for any rates a feasible
flow is optimal iff it is at Nash equilibrium. -/
theorem corollary_4_2 {J R Sd : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (s : Fin R → Fin Sd) (rate : Fin Sd → ℝ) (hrate : ∀ i, 0 < rate i)
    (a : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j)
    (x : Fin R → ℝ) (hx : x ∈ wardropFeasible s rate) :
    IsOptimalFlow A s (linLatency a (fun _ => 0)) rate x ↔
      SelfishRouting.Bicriteria.IsNashFlow A s (linLatency a (fun _ => 0)) rate x := by sorry

end SelfishRouting.Linear
