-- Prove2me | Theorems.Thm_SelfishRouting_Linear_cost_half_flow
-- name    : SelfishRouting.Linear.cost_half_flow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:56.484078+00:00
-- url     : https://prove2.me/theorems/dfda5741-d141-4a94-9570-ed667df2bda0
-- title:
--   Proof of Theorem 4.5, second display — $C(f/2)\ge\frac14 C(f)$ for linear latencies
-- statement:
--   Let every edge have a linear latency $\ell_e(x)=a_ex+b_e$ with $a_e,b_e\ge 0$ and let the route incidences be $0/1$. For every flow $f$ with $f_P\ge 0$ on every route,
--   $$C(f/2)=\sum_e\Big(\tfrac14a_ef_e^2+\tfrac12b_ef_e\Big)\ \ge\ \tfrac14\sum_e\big(a_ef_e^2+b_ef_e\big)=\tfrac14C(f).$$
--
--   In the proof of Theorem 4.5 this bounds the cost of the first stage, the optimal flow $f/2$ for the rates $r/2$, from below by a quarter of the equilibrium cost.
--
--   **Formalization Note** Stated as $C(f)\le 4\,C(f/2)$, with no division. The page applies it to a Nash flow; equilibrium is not needed, only nonnegative route flows (so that the edge flows are nonnegative).
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 17, proof of Theorem 4.5, second display

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Linear_Model
import Definitions.Def_SelfishRouting_Linear_LinearLatency

namespace SelfishRouting.Linear

/-- Proof of Theorem 4.5, second display (p. 17): with linear latencies with `a_e, b_e ≥ 0`,
`C(f/2) ≥ ¼ C(f)` for every flow `f` with nonnegative route flows. -/
theorem cost_half_flow {J R : ℕ} (A : Fin J → Fin R → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (a b : Fin J → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (x : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) :
    SelfishRouting.Bicriteria.cost A (linLatency a b) x ≤ 4 * SelfishRouting.Bicriteria.cost A (linLatency a b) (fun r => x r / 2) := by sorry

end SelfishRouting.Linear
