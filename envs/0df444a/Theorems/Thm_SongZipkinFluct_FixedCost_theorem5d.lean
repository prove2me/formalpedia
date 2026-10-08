-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_theorem5d
-- name    : SongZipkinFluct.FixedCost.theorem5d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:39.01834+00:00
-- url     : https://prove2.me/theorems/7d26063f-c5be-4a98-863b-e0d00e860691
-- title:
--   Theorem 5(d) — W_∞ and G_∞ satisfy the optimality equation (2)
-- statement:
--   In the fixed-cost model (standing hypotheses, $\alpha\bar c < p$, $K > 0$, $W_0 = W_\infty$ of the linear model), the limits $W_\infty$, $G_\infty$ satisfy the optimality equation (2): for all $i$ and $x$ the minimum below is attained and
--   $$
--   W_\infty(i, x) = \min_{y \ge x}\{K\delta(y - x) + G_\infty(i, y)\},
--   $$
--   and for all $i$ and $y$
--   $$
--   G_\infty(i, y) = G^+(i, y) + \beta\lambda_i c + \beta\Big\{\lambda_i W_\infty(i, y-1) + \sum_{j\ne i} q_{ij}W_\infty(j, y) + (\mu - \lambda_i - q_i)W_\infty(i, y)\Big\}.
--   $$
--
--   Equation (2) is the transformed form $W = cx + V$ of the infinite-horizon optimality equation (1), so this identifies $W_\infty$ as a solution of the Bellman equation of the fixed-cost problem.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 359, Theorem 5(d); p. 355, (2)

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

open Filter Topology

namespace SongZipkinFluct.FixedCost

open Model

/-- Theorem 5(d) (p. 359) of Song and Zipkin (1993). Fixed-cost model of §3.2
(`K = K̄F̃_L(α) > 0`, `W₀ = W_∞` of the linear model). The limits `W_∞`, `G_∞` satisfy the
optimality equation (2) (p. 355):
`W_∞(i, x) = min_{y ≥ x} {Kδ(y − x) + G_∞(i, y)}` (the minimum is attained) and
`G_∞(i, y) = G⁺(i, y) + βλ_i c + β{λ_i W_∞(i, y − 1) + Σ_{j≠i} q_ij W_∞(j, y) + (μ − λ_i − q_i) W_∞(i, y)}`.
-/
theorem theorem5d {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar) :
    (∀ (i : I) (x : ℤ), IsLeast
        (Set.range fun y : {y : ℤ // x ≤ y} => M.K * SongZipkinFluct.Linear.delta (y.1 - x) + GinfK M i y.1)
        (WinfK M i x)) ∧
      ∀ (i : I) (y : ℤ), GinfK M i y = contG M (WinfK M) i y := by sorry

end SongZipkinFluct.FixedCost
