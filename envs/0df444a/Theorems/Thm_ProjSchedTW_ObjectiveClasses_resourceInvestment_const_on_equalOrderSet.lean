-- Prove2me | Theorems.Thm_ProjSchedTW_ObjectiveClasses_resourceInvestment_const_on_equalOrderSet
-- name    : ProjSchedTW.ObjectiveClasses.resourceInvestment_const_on_equalOrderSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:44:41.033143+00:00
-- url     : https://prove2.me/theorems/8599a118-a299-4495-8c0c-55f7e481e946
-- title:
--   Proposition 3.3.5 — the resource investment objective is constant on equal-order sets
-- statement:
--   Let $c_k\ge 0$ be the procurement cost per unit of resource $k\in\mathcal R$ and let
--   $$f(S)=\sum_{k\in\mathcal R}c_k\max_{t}r_k(S,t)$$
--   be the resource investment objective, where $r_k(S,t)$ is the amount of resource $k$ used at time $t$ under schedule $S$. Then for each feasible schedule $S\in\mathcal S$, $f$ is constant on the equal-order set $\mathcal S_T^{=}(O(S))$: $f(S')=f(S'')$ for all $S',S''\in\mathcal S_T^{=}(O(S))$.
--
--   Together with Proposition 3.3.6 this places the resource investment objective in class 6 of locally regular functions.
--
--   **Formalization Note** The maximum over $t$ is taken over all $t\ge 0$; on time-feasible schedules every activity ends by $S_{n+1}\le\bar d$, so this is the book's maximum over $0\le t\le\bar d$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, DOI 10.1007/978-3-540-24800-2, p. 229, Proposition 3.3.5 (objective from p. 203)

import Mathlib
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Project
import Definitions.Def_ProjSchedTW_ObjectiveClasses_Classes

namespace ProjSchedTW.ObjectiveClasses

/-- Proposition 3.3.5 (p. 229): for each `S ∈ 𝒮`, the resource investment objective
`∑ c_k max r_kt` is constant on the equal-order set `S_T^=(O(S))`. -/
theorem resourceInvestment_const_on_equalOrderSet {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (c : K → ℝ) (hc : ∀ k, 0 ≤ c k)
    (S : Fin (n + 2) → ℝ) (hS : S ∈ feasibleSet P) :
    ∀ S' ∈ equalOrderSet P S, ∀ S'' ∈ equalOrderSet P S,
      resourceInvestment P c S' = resourceInvestment P c S'' := by sorry

end ProjSchedTW.ObjectiveClasses
