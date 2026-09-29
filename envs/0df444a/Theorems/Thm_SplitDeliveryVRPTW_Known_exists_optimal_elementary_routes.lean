-- Prove2me | Theorems.Thm_SplitDeliveryVRPTW_Known_exists_optimal_elementary_routes
-- name    : SplitDeliveryVRPTW.Known.exists_optimal_elementary_routes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:50:24.393951+00:00
-- url     : https://prove2.me/theorems/f4dd023b-c67e-402a-8ad9-47c7e98e4afb
-- title:
--   Remark 1 — some optimal SDVRPTW solution has only elementary routes
-- statement:
--   Let an instance of the split-delivery vehicle routing problem with time windows be given: capacity $Q$, positive demands $d_i$, time windows $[e_v, l_v]$, travel times $t_{vw}$ and costs $c_{vw}$, with arc set $\mathcal A$. Suppose that travel times and costs satisfy the triangle inequality, and that the instance admits at least one feasible solution. Then there exists an optimal solution $r_1, \dots, r_m$ in which each route visits each customer at most once:
--   $$
--   \text{for every } f, \text{ the customer sequence } (v^f_1, \dots, v^f_{m_f}) \text{ of } r_f \text{ has no repeated entry.}
--   $$
--
--   This remark justifies restricting the column-generation subproblem of a branch-and-price method to elementary paths from $0$ to $n+1$ that satisfy the capacity and time-window constraints.
--
--   **Formalization Note** The paper states "there exists an optimal solution to this instance" without a hypothesis; an instance with no feasible solution has no optimal solution, so the Lean statement assumes feasibility, the weakest hypothesis under which the claim can hold. Routes are allowed to repeat customers in the definition of a solution, so the property is a genuine restriction and not built into the model.
-- source:
--   Desaulniers, Branch-and-Price-and-Cut for the Split-Delivery Vehicle Routing Problem with Time Windows, Operations Research 58(1):179–192 (2010), https://doi.org/10.1287/opre.1090.0713, p. 181, Section 2, Remark 1

import Mathlib
import Definitions.Def_SplitDeliveryVRPTW_Known_Instance
import Definitions.Def_SplitDeliveryVRPTW_Known_Solution

namespace SplitDeliveryVRPTW.Known

/-- Remark 1 (Desaulniers 2010, p. 181): for an SDVRPTW instance whose costs and travel times
satisfy the triangle inequality, and which admits a feasible solution, some optimal solution
has only elementary routes: no route visits a customer twice. -/
theorem exists_optimal_elementary_routes {n : ℕ} (I : Instance n)
    (hTri : I.TriangleInequality) (hFeas : ∃ S : Solution I, S.Feasible) :
    ∃ S : Solution I, S.IsOptimal ∧ ∀ f, (S.routes f).visits.Nodup := by sorry

end SplitDeliveryVRPTW.Known
