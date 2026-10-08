-- Prove2me | Theorems.Thm_RoslingAssembly_Unbounded_theorem4i_cost_unbounded_below
-- name    : RoslingAssembly.Unbounded.theorem4i_cost_unbounded_below
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:25.487506+00:00
-- url     : https://prove2.me/theorems/1092141e-d094-4486-8bce-3710197088b1
-- title:
--   Theorem 4(i), p. 574 — if an item and its predecessors have negative discounted echelon holding cost, the minimal cost of P is unbounded below
-- statement:
--   Consider Problem P for an assembly system with items $1, \dots, N$ ($N \ge 1$, item 1 the end item, a tree with $s(1) = 0$ and $1 \le s(i) < i$ for $i \ge 2$, indexed so that $M_{i-1} \le M_i$), demands $\xi_1, \xi_2, \dots$ independent with a common law that has a density, $\xi_t \ge 0$ and $0 < E\xi_t < \infty$, discount factor $0 < \alpha < 1$, and well-formed initial positions $x^0$. No sign condition is imposed on the echelon holding costs $h_i$, on $p$ or on $H_1$.
--
--   If for some item $i$
--   $$h_i\,\alpha^{-M_{s(i)}} + \sum_{k \in B(i)} h_k\,\alpha^{-M_{s(k)}} < 0,$$
--   then the minimal cost of Problem P is unbounded below: for every real number $C$ there is a measurable policy $\pi$, feasible from $x^0$, whose cost (2) is a real number $r$ with
--   $$r < C.$$
--
--   This is the "practical necessity" half of the Generalized Assumption (i): an item which, together with all its predecessors, has negative discounted echelon holding cost makes the model degenerate, since stockpiling it forever earns money.
--
--   **Formalization Note.** "Unbounded below" is stated with witnesses of *real* cost: in the extended reals the cost of a policy whose positive and negative parts are both infinite is $\top - \top = \bot$, and such a policy would trivially lie below every $C$. The page allows $\alpha = 1$ (average cost); this statement is for $0 < \alpha < 1$. The constant of (2) is dropped, which shifts every cost by the same amount. The well-formedness of $x^0$ (the history before period 1 obeys (3) and nonnegative ordering) is taken for granted on the page and makes Problem P feasible.
-- source:
--   Rosling, Optimal Inventory Policies for Assembly Systems under Random Demands, Oper. Res. 37(4), 1989, p. 574, Theorem 4 (i)

import Mathlib
import Definitions.Def_RoslingAssembly_Unbounded_Model

namespace RoslingAssembly.Unbounded

open MeasureTheory

/-- Theorem 4(i), p. 574: if `h_i α^{−M_{s(i)}} + ∑_{k ∈ B(i)} h_k α^{−M_{s(k)}} < 0` for some
item `i`, then the minimal cost of Problem P is unbounded below: for every real `C` there is a
measurable policy, feasible from `x0`, whose cost is a real number below `C`. -/
theorem theorem4i_cost_unbounded_below (S : Model) (x0 : ℕ → ℕ → ℝ)
    (hT : S.IsTree) (hI : S.IsIndexed) [IsProbabilityMeasure S.ν] (hD : S.DemandStanding)
    (hα0 : 0 < S.α) (hα1 : S.α < 1) (hx0 : S.WellFormed x0)
    (i : ℕ) (hi : i ∈ S.items) (hneg : S.echelonSum i < 0) :
    ∀ C : ℝ, ∃ π : RoslingAssembly.SeriesEquiv.Policy, IsMeasurablePolicy π ∧ S.Feasible x0 π ∧
      ∃ r : ℝ, S.cost π = (r : EReal) ∧ r < C := by sorry

end RoslingAssembly.Unbounded
