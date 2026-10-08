-- Prove2me | Theorems.Thm_SongZipkinFluct_Linear_theorem2
-- name    : SongZipkinFluct.Linear.theorem2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:44.892093+00:00
-- url     : https://prove2.me/theorems/407c110f-4a3d-49ed-bbbd-03257cb3300e
-- title:
--   Theorem 2 — infinite-horizon world-dependent basestock optimality
-- statement:
--   In the linear-order-cost model, under $\alpha\bar c<p$, every world state $i$ has a finite smallest global minimizer $y^*(i)$ of the limiting cost $G_\infty(i,\cdot)$. The finite-stage minimizers converge to a level $y_\infty^*(i)$, and the myopic, limiting and optimal levels satisfy
--
--   $$0\le y^+_{\min}\le y^*(i)\le y_\infty^*(i)\le y^+(i).$$
--
--   The level $y_\infty^*(i)$ also minimizes $G_\infty(i,\cdot)$. The stationary world-dependent basestock policy that orders to $\max\{x,y^*(i)\}$ in state $(i,x)$ minimizes infinite-horizon expected discounted cost from every state among all feasible history-dependent policies.
--
--   **Formalization Note** The policy-cost recursion uses the uniformized version of equation (1), with nonnegative extended-real costs. Its policy comparison includes every feasible deterministic history-dependent policy.
--
--   The cost of this basestock policy is finite from every initial state; this prevents an all-infinite-cost reading of optimality.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, pp. 357–358, Theorem 2(b), (c), (e)

import Mathlib
import Definitions.Def_SongZipkinFluct_Linear_Dynamics

namespace SongZipkinFluct.Linear

/-- Song and Zipkin (1993), Theorem 2(b), (c), (e), pp. 357--358.
The existence of the finite smallest minimizers and their limiting
integer levels is asserted, not assumed. The basestock policy is
optimal from every initial state among all feasible deterministic
history-dependent policies of the uniformized infinite-horizon MDP
of equation (1). Randomization is omitted because it cannot improve
nonnegative expected costs in this countable-state model. -/
theorem theorem2 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hA : M.Assumption1) :
    ∃ (ys : ℕ → I → ℤ) (yplus ystar yinf : I → ℤ) (ymin : ℤ),
      (∀ i : I, SmallestMinimizer (M.Gplus i) (yplus i)) ∧
      IsLeast (Set.range yplus) ymin ∧
      (∀ n : ℕ, 1 ≤ n → ∀ i : I,
        SmallestMinimizer (M.Glin n i) (ys n i)) ∧
      (∀ i : I, Filter.Tendsto (fun n : ℕ => ys (n + 1) i)
        Filter.atTop (nhds (yinf i))) ∧
      (∀ i : I, SmallestMinimizer (M.Ginf i) (ystar i)) ∧
      0 ≤ ymin ∧
      (∀ i : I,
        ymin ≤ ystar i ∧ ystar i ≤ yinf i ∧ yinf i ≤ yplus i ∧
        ∀ y : ℤ, M.Ginf i (yinf i) ≤ M.Ginf i y) ∧
      M.IsOptimal 0 (baseStock ystar) ∧
      (∀ s : State I, M.policyCost 0 (baseStock ystar) [] s < ⊤) := by sorry

end SongZipkinFluct.Linear
