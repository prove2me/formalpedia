-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_ystar_exists
-- name    : SongZipkinFluct.FixedCost.ystar_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T05:51:07.789453+00:00
-- url     : https://prove2.me/theorems/8acad341-ddfa-4db2-9fc8-60191b4eeb5d
-- title:
--   Theorem 2(b) — the linear-model limit $G_0(i,\cdot) = G_\infty(i,\cdot)$ has a smallest minimizer $y^*(i)$
-- statement:
--   Consider the fluctuating-demand inventory model under the standing hypotheses and Assumption 1 ($\alpha\bar c < p$). Let $G_0(i,\cdot) = G_\infty(i,\cdot)$ be the limit of the linear order-cost model (fixed cost $K=0$, terminal cost $W_0\equiv 0$), i.e. $G_0(i,y) = \sup_{n\ge1} G_n(i,y)$ for the value iteration (10).
--
--   **Claim (Theorem 2(b)).** For every world state $i$, the function $y\mapsto G_0(i,y)$ on $\mathbb Z$ has a smallest global minimizer $y^*(i)$ (it is convex and tends to $+\infty$ as $|y|\to\infty$). This $y^*(i)$ is the optimal world-dependent base-stock level of the linear model, and serves as the lower bound $y^*(i)\le S^*(i)$ in the fixed-cost model.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 357, Theorem 2(b) (y*(i) as used on p. 358)

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

namespace SongZipkinFluct.FixedCost

open Model

/-- Song and Zipkin (1993), Theorem 2(b), p. 357, in the encoding of the fixed-cost model:
under the standing hypotheses and Assumption 1 (`αc̄ < p`), for every world state `i` the limit
`G₀(i, ·) = G_∞(i, ·)` of the linear order-cost model (`K = 0`, `W₀ ≡ 0`) has a smallest global
minimizer `y*(i)`. -/
theorem ystar_exists {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) :
    ∃ ystar, IsYStar M ystar := by
  sorry

end SongZipkinFluct.FixedCost
