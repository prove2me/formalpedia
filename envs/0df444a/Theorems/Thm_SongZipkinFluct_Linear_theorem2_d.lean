-- Prove2me | Theorems.Thm_SongZipkinFluct_Linear_theorem2_d
-- name    : SongZipkinFluct.Linear.theorem2_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:43.987201+00:00
-- url     : https://prove2.me/theorems/9757b9b1-26d8-4b90-a6cf-a0c6baf53920
-- title:
--   Theorem 2(d) — the limit solves the optimality equation
-- statement:
--   The pointwise limits $W_\infty$ and $G_\infty$ satisfy the zero-fixed-cost optimality equation (2). For each state $(i,x)$, its minimum over feasible order-up-to positions is attained both by the smallest global minimizer $y^*(i)$ and by the limiting finite-stage level $y_\infty^*(i)$, after taking the maximum with $x$.
--
--   $$W_\infty(i,x)=\min_{y\ge x}G_\infty(i,y)=G_\infty(i,\max\{x,y^*(i)\})=G_\infty(i,\max\{x,y_\infty^*(i)\}).$$
--
--   This identifies the basestock decisions that solve the limit equation.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 358, Theorem 2(d)

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Dynamics

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Theorem 2(d), p. 358. Equation (2) at
`K=0` says `G∞=contG W∞` and `W∞` is its minimum over feasible
order-up-to levels. The displayed equalities attest both minimizers. -/
theorem theorem2_d {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hA : M.Assumption1) :
    ∃ (ys : ℕ → I → ℤ) (ystar yinf : I → ℤ),
      (∀ n : ℕ, 1 ≤ n → ∀ i : I,
        SmallestMinimizer (M.Glin n i) (ys n i)) ∧
      (∀ i : I, Filter.Tendsto (fun n : ℕ => ys (n + 1) i)
        Filter.atTop (nhds (yinf i))) ∧
      (∀ i : I, SmallestMinimizer (M.Ginf i) (ystar i)) ∧
      (∀ i : I, ∀ y : ℤ, M.Ginf i (yinf i) ≤ M.Ginf i y) ∧
      (∀ i : I, ∀ y : ℤ, M.Ginf i y = M.contG M.Winf i y) ∧
      ∀ i : I, ∀ x : ℤ,
        (∀ y : ℤ, x ≤ y → M.Winf i x ≤ M.Ginf i y) ∧
        M.Winf i x = M.Ginf i (max x (ystar i)) ∧
        M.Winf i x = M.Ginf i (max x (yinf i)) := by sorry

end SongZipkinFluct.Linear
