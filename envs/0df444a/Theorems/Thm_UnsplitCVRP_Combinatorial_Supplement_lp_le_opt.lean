-- Prove2me | Theorems.Thm_UnsplitCVRP_Combinatorial_Supplement_lp_le_opt
-- name    : UnsplitCVRP.Combinatorial.Supplement.lp_le_opt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T09:40:32.723156+00:00
-- url     : https://prove2.me/theorems/2b44580a-6312-48f8-a0c2-bf115784699a
-- title:
--   §4, p. 9 — the optimum of the Configuration-LP is a lower bound on opt
-- statement:
--   Consider an instance of the CVRP with unsplittable demands: clients $V$, depot $r$, metric costs $c$, demands $d_v\in(0,1]$ and vehicle capacity $1$. Fix a threshold $\delta$, call a client big if $d_v>\delta$, let $\mathcal J$ be the set of feasible tours consisting of the depot and some big clients, and let $x^*$ be an optimal solution of the Configuration-LP
--   $$\min\ \sum_{T\in\mathcal J}c(T)\,x_T\quad\text{s.t.}\quad\sum_{T\in\mathcal J:\,v\in T}x_T\ge1\ \ (v\in V_{big}),\qquad x\ge0 .$$
--   Then for every feasible solution $R$ of the instance,
--   $$\operatorname{cost}(x^*)\ =\ \sum_{T\in\mathcal J}c(T)\,x^*_T\ \le\ c(R).$$
--
--   The paper obtains this by shortcutting the tours of an optimal solution past the small clients and discarding tours without big clients, which gives an integer solution of the LP of cost at most opt. It is the bound $\gamma\cdot\operatorname{cost}(x^*)\le\gamma\cdot\mathrm{opt}$ in display (8) of the proof of Theorem 2.
--
--   **Formalization Note** Comparing with every feasible solution is equivalent to comparing with opt.
--
--   Differences from the source:
--   - generalization: δ a fixed constant in (0, 1/2] → any real δ; reason: the shortcutting argument works for every threshold, in particular those in (0, 1/2]
-- source:
--   Friggstad, Mousavi, Rahgoshay, Salavatipour, Improved Approximations for CVRP with Unsplittable Demands, arXiv:2111.08138v1, p. 9, §4 (paragraph after the Configuration-LP)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_UnsplitCVRP_Combinatorial_Setting
import Definitions.Def_UnsplitCVRP_Combinatorial_Supplement_ConfigLP

namespace UnsplitCVRP.Combinatorial.Supplement

/-- §4, p. 9: the optimum value of the Configuration-LP is a lower bound on the cost of
every feasible solution ("the optimum LP value provides a lower bound on opt"). -/
theorem lp_le_opt {n : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hc : SupplyChainTheory.VRPMetric c) (d : Fin (n + 1) → ℝ)
    (hd : Demands d) (δ : ℝ)
    (xstar : List (Fin (n + 1)) → ℝ) (hx : IsConfigOptimal c d δ xstar)
    (R : List (List (Fin (n + 1)))) (hR : IsSolution d R) :
    configCost c d δ xstar ≤ SupplyChainTheory.solutionCost c R := by sorry

end UnsplitCVRP.Combinatorial.Supplement
