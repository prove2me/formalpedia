-- Prove2me | Theorems.Thm_SplitDeliveryVRPTW_Known_exists_optimal_reverse_arc_pair_at_most_once
-- name    : SplitDeliveryVRPTW.Known.exists_optimal_reverse_arc_pair_at_most_once
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:52:08.996699+00:00
-- url     : https://prove2.me/theorems/c467752a-d987-4f93-8d41-416b8f9f5b33
-- title:
--   Corollary 2 — some optimal SDVRPTW solution traverses each pair of reverse customer arcs at most once
-- statement:
--   Let an instance of the split-delivery vehicle routing problem with time windows be given: capacity $Q$, positive demands $d_i$, time windows $[e_v, l_v]$, travel times $t_{vw}$ and costs $c_{vw}$, with arc set $\mathcal A$, and let $\mathcal A(\mathcal N) = \mathcal A \cap (\mathcal N \times \mathcal N)$ be the arcs linking two customers. Suppose that travel times and costs satisfy the triangle inequality, and that the instance admits at least one feasible solution. Then there exists an optimal solution such that, writing $x_{ij}$ for the number of traversals of arc $(i, j)$ summed over all routes of the solution,
--   $$
--   x_{ij} + x_{ji} \le 1 \qquad \text{for every } (i, j) \in \mathcal A(\mathcal N) .
--   $$
--   In words: the two arcs of every pair of reverse customer arcs are traversed at most once in total, and every customer arc without a reverse arc is traversed at most once.
--
--   This strengthening of Corollary 1 yields the family of valid inequalities (7) that the paper adds to its arc-flow formulation and handles as cutting planes in its branch-and-price-and-cut method.
--
--   **Formalization Note** The paper states the corollary through a set $\mathcal A^*(\mathcal N) \subseteq \mathcal A$ containing exactly one arc of each pair of reverse arcs in $\mathcal A(\mathcal N)$ and every arc of $\mathcal A(\mathcal N)$ whose reverse is not in $\mathcal A$, and through $\mathcal A^*_{ij} = \{(i,j)\}$ or $\{(i,j),(j,i)\}$; it writes that "at most one arc in set $\mathcal A^*_{ij}$ appears at most once for each arc $(i,j) \in \mathcal A^*(\mathcal N)$". Constraint (7) (p. 182), which "ensue[s] from Corollary 2", fixes the meaning: $\sum_f \sum_{(i,j) \in \mathcal A^*_{i'j'}} x^f_{ij} \le 1$, i.e. the total number of traversals of the arcs of $\mathcal A^*_{ij}$ is at most one. An arc outside $\mathcal A$ is never traversed, and the condition $x_{ij} + x_{ji} \le 1$ is symmetric in $i, j$, so stating it for every $(i, j) \in \mathcal A(\mathcal N)$ is equivalent to the paper's statement for every admissible choice of $\mathcal A^*(\mathcal N)$. Feasibility of the instance is assumed as the weakest hypothesis under which an optimal solution exists.
-- source:
--   Desaulniers, Branch-and-Price-and-Cut for the Split-Delivery Vehicle Routing Problem with Time Windows, Operations Research 58(1):179–192 (2010), https://doi.org/10.1287/opre.1090.0713, p. 181, Section 2, Corollary 2 and the definitions of reverse arcs, A*(N) and A*_ij before it; p. 182, Section 3, constraint (7)

import Mathlib
import Definitions.Def_SplitDeliveryVRPTW_Known_Instance
import Definitions.Def_SplitDeliveryVRPTW_Known_Solution

namespace SplitDeliveryVRPTW.Known

/-- Corollary 2 (Desaulniers 2010, p. 181), in the form fixed by constraint (7) (p. 182): for
an SDVRPTW instance whose costs and travel times satisfy the triangle inequality, and which
admits a feasible solution, some optimal solution traverses, summed over all routes, the arcs
of each set `𝒜*_ij` at most once in total: for every customer arc `(i, j) ∈ 𝒜(𝒩)`, the
number of traversals of `(i, j)` plus the number of traversals of `(j, i)` is at most one.
(When `(j, i) ∉ 𝒜` it is never traversed, so this is the paper's statement for every choice
of `𝒜*(𝒩)`.) -/
theorem exists_optimal_reverse_arc_pair_at_most_once {n : ℕ} (I : Instance n)
    (hTri : I.TriangleInequality) (hFeas : ∃ S : Solution I, S.Feasible) :
    ∃ S : Solution I, S.IsOptimal ∧
      ∀ i j : Fin n, I.IsArc (.cust i) (.cust j) →
        S.arcCount i j + S.arcCount j i ≤ 1 := by sorry

end SplitDeliveryVRPTW.Known
