-- Prove2me | Theorems.Thm_SplitDeliveryVRPTW_Known_exists_optimal_arc_at_most_once
-- name    : SplitDeliveryVRPTW.Known.exists_optimal_arc_at_most_once
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:51:38.526262+00:00
-- url     : https://prove2.me/theorems/a23c3a8d-7738-4215-8bec-5b15dddc37bb
-- title:
--   Corollary 1 — some optimal SDVRPTW solution uses each customer arc at most once
-- statement:
--   Let an instance of the split-delivery vehicle routing problem with time windows be given: capacity $Q$, positive demands $d_i$, time windows $[e_v, l_v]$, travel times $t_{vw}$ and costs $c_{vw}$, with arc set $\mathcal A$, and let $\mathcal A(\mathcal N) = \mathcal A \cap (\mathcal N \times \mathcal N)$ be the arcs linking two customers. Suppose that travel times and costs satisfy the triangle inequality, and that the instance admits at least one feasible solution. Then there exists an optimal solution in which each arc of $\mathcal A(\mathcal N)$ appears at most once: writing $x_{ij}$ for the number of traversals of arc $(i, j)$, summed over all routes of the solution,
--   $$
--   x_{ij} \le 1 \qquad \text{for every } (i, j) \in \mathcal A(\mathcal N) .
--   $$
--
--   Gendreau et al. (2006) proposed this corollary of Theorem 1 because, unlike Theorem 1, it can be imposed directly on arc-flow variables in a branch-and-price method.
--
--   **Formalization Note** "Appears at most once" is read as a count over the whole solution (all routes, all positions), as in constraint (7) of the paper for single arcs. Feasibility of the instance is assumed as the weakest hypothesis under which an optimal solution exists.
-- source:
--   Desaulniers, Branch-and-Price-and-Cut for the Split-Delivery Vehicle Routing Problem with Time Windows, Operations Research 58(1):179–192 (2010), https://doi.org/10.1287/opre.1090.0713, p. 181, Section 2, Corollary 1 (Gendreau et al. 2006) and the definition of A(N) before it

import Mathlib
import Definitions.Def_SplitDeliveryVRPTW_Known_Instance
import Definitions.Def_SplitDeliveryVRPTW_Known_Solution

namespace SplitDeliveryVRPTW.Known

/-- Corollary 1 (Desaulniers 2010, p. 181; Gendreau et al. 2006): for an SDVRPTW instance whose
costs and travel times satisfy the triangle inequality, and which admits a feasible solution,
some optimal solution traverses each customer arc `(i, j) ∈ 𝒜(𝒩)` at most once, counted over
all routes. -/
theorem exists_optimal_arc_at_most_once {n : ℕ} (I : Instance n)
    (hTri : I.TriangleInequality) (hFeas : ∃ S : Solution I, S.Feasible) :
    ∃ S : Solution I, S.IsOptimal ∧
      ∀ i j : Fin n, I.IsArc (.cust i) (.cust j) → S.arcCount i j ≤ 1 := by sorry

end SplitDeliveryVRPTW.Known
