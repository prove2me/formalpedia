-- Prove2me | Theorems.Thm_SplitDeliveryVRPTW_Known_exists_optimal_split_customers
-- name    : SplitDeliveryVRPTW.Known.exists_optimal_split_customers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:50:55.415631+00:00
-- url     : https://prove2.me/theorems/19c29ec0-8630-41ad-a5d3-7b7a84371ee3
-- title:
--   Theorem 1 — some optimal SDVRPTW solution has no two routes sharing two split customers
-- statement:
--   Let an instance of the split-delivery vehicle routing problem with time windows be given: capacity $Q$, positive demands $d_i$, time windows $[e_v, l_v]$, travel times $t_{vw}$ and costs $c_{vw}$, with arc set $\mathcal A$. Suppose that travel times and costs satisfy the triangle inequality, and that the instance admits at least one feasible solution. Then there exists an optimal solution $r_1, \dots, r_m$ in which no two routes have more than one split customer in common: for all route indices $a \ne b$ and all customers $i, j$,
--   $$
--   i, j \text{ are both visited by } r_a \text{ and by } r_b \ \Longrightarrow\ i = j .
--   $$
--
--   This property was established by Dror and Trudeau for the split-delivery VRP without time windows; Gendreau et al. (2006) observed that it holds with time windows as well. It underlies the valid inequalities used in branch-and-price methods for split-delivery routing.
--
--   **Formalization Note** The paper does not define "split customer" or "in common". A customer is read as *split* when at least two distinct routes of the solution visit it, and two routes have a customer *in common* when both visit it; a customer visited by two distinct routes is split by definition, so the statement becomes: two distinct routes share at most one customer. This visit-based reading is at least as strong as a delivery-based one (both routes delivering a positive quantity), because deliveries occur only at visits. Two routes are distinct when their indices differ, even if they drive the same walk. Feasibility of the instance is assumed as the weakest hypothesis under which an optimal solution exists.
-- source:
--   Desaulniers, Branch-and-Price-and-Cut for the Split-Delivery Vehicle Routing Problem with Time Windows, Operations Research 58(1):179–192 (2010), https://doi.org/10.1287/opre.1090.0713, p. 181, Section 2, Theorem 1 (Dror and Trudeau 1989, 1990; Gendreau et al. 2006)

import Mathlib
import Definitions.Def_SplitDeliveryVRPTW_Known_Instance
import Definitions.Def_SplitDeliveryVRPTW_Known_Solution

namespace SplitDeliveryVRPTW.Known

/-- Theorem 1 (Desaulniers 2010, p. 181; Dror–Trudeau): for an SDVRPTW instance whose costs
and travel times satisfy the triangle inequality, and which admits a feasible solution, some
optimal solution has no two routes with more than one split customer in common: if two
distinct routes `a ≠ b` both visit customers `i` and `j`, then `i = j`. -/
theorem exists_optimal_split_customers {n : ℕ} (I : Instance n)
    (hTri : I.TriangleInequality) (hFeas : ∃ S : Solution I, S.Feasible) :
    ∃ S : Solution I, S.IsOptimal ∧
      ∀ a b : Fin S.m, a ≠ b → ∀ i j : Fin n,
        i ∈ (S.routes a).visits → i ∈ (S.routes b).visits →
        j ∈ (S.routes a).visits → j ∈ (S.routes b).visits → i = j := by sorry

end SplitDeliveryVRPTW.Known
