-- Prove2me | Theorems.Thm_ProjSchedTW_NetPresentValue_exists_optimal_vertex
-- name    : ProjSchedTW.NetPresentValue.exists_optimal_vertex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:25:02.286288+00:00
-- url     : https://prove2.me/theorems/0987cd8a-34e5-4906-a3ec-e6097f57572f
-- title:
--   §3.9.1 — the net present value problem has an optimal vertex schedule
-- statement:
--   Let $0<\beta\le1$ and let $c_i^F\in\mathbb R$ be arbitrary cash flows. Suppose the time-feasible region $\mathcal S_T$ is nonempty and bounded. Then problem
--   $$\min\ f(S)=-\sum_{i\in V}c_i^F\beta^{S_i+p_i}\quad\text{subject to}\quad S\in\mathcal S_T$$
--   has an optimal solution $S$ that is a vertex (extreme point) of $\mathcal S_T$.
--
--   This is the first of the two observations on which the optimality criterion of Proposition 3.9.2 rests: it lets the search for an optimal schedule be confined to the finitely many vertices of $\mathcal S_T$.
--
--   **Formalization Note** The book states that $\mathcal S_T$ is bounded because of the deadline $S_{n+1}\le\bar d$ (p. 198); boundedness of every other start time needs the standing arcs of Remarks 1.1.2, so it is stated here as a hypothesis, together with $\mathcal S_T\neq\emptyset$. Without boundedness the infimum of $f$ need not be attained.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 333, §3.9.1 (first basic observation); p. 198 (S_T is a polytope)

import Mathlib
import Definitions.Def_ProjSchedTW_NetPresentValue_Project

namespace ProjSchedTW.NetPresentValue

/-- §3.9.1 (p. 333), first basic observation, with §3.1 (p. 198): for a discount rate
`0 < β ≤ 1` and arbitrary cash flows, if the time-feasible region `S_T` is nonempty and bounded
(a polytope, as §3.1 states for `PS∞|temp, d̄|f`), then problem (3.9.1) has an optimal solution
that is a vertex (extreme point) of `S_T`. -/
theorem exists_optimal_vertex {n : ℕ} (P : Project n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (c : Fin (n + 2) → ℝ) (hne : (timeFeasibleSet P).Nonempty)
    (hbdd : Bornology.IsBounded (timeFeasibleSet P)) :
    ∃ S ∈ (timeFeasibleSet P).extremePoints ℝ, IsTimeOptimal P β c S := by sorry

end ProjSchedTW.NetPresentValue
