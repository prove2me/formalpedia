-- Prove2me | Theorems.Thm_ProjSchedTW_NetPresentValue_npv_binary_monotone_sum_separable
-- name    : ProjSchedTW.NetPresentValue.npv_binary_monotone_sum_separable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:25:53.742815+00:00
-- url     : https://prove2.me/theorems/33914856-7d90-4c6f-a657-be01e38f75a4
-- title:
--   §3.3.5 — the net present value objective is binary-monotone and sum-separable
-- statement:
--   Let $0<\beta\le1$ be a discount rate, $c_i^F\in\mathbb R$ arbitrary cash flows and $p_i$ the durations of a project. Then the net present value objective
--   $$f(S)=-\sum_{i\in V}c_i^F\beta^{S_i+p_i}$$
--   is binary-monotone: on every (half-)line $\{S+\lambda z\ge0\mid\lambda\in\mathbb R\}$ with direction $z\in\{0,1\}^{n+2}$ it is either nondecreasing or nonincreasing in $\lambda$. It is also sum-separable, $f(S)=\sum_{i\in V}f_i(S_i)$ with $f_i(S_i)=-c_i^F\beta^{S_i+p_i}$.
--
--   This places the net present value problem in the class of binary-monotone objectives, for which an optimal schedule can be found among the vertices of the feasible region.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, pp. 224–225, §3.3.5 (unnumbered statement after Definition 3.3.2)

import Mathlib
import Definitions.Def_ProjSchedTW_NetPresentValue_Project
import Definitions.Def_ProjSchedTW_NetPresentValue_Objective

namespace ProjSchedTW.NetPresentValue

/-- §3.3.5 (pp. 224–225): for a discount rate `0 < β ≤ 1` and arbitrary cash flows `c_i^F ∈ ℝ`,
the net present value objective `f(S) = −∑_{i ∈ V} c_i^F β^{S_i + p_i}` of Section 3.1 is
binary-monotone (Definition 3.3.2) and sum-separable (Eq. (3.3.1)). -/
theorem npv_binary_monotone_sum_separable {n : ℕ} (P : Project n) (β : ℝ) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (c : Fin (n + 2) → ℝ) :
    IsBinaryMonotone (npvObjective P β c) ∧ IsSumSeparable (npvObjective P β c) := by sorry

end ProjSchedTW.NetPresentValue
