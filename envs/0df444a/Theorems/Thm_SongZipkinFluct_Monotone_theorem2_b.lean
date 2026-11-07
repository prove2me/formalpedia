-- Prove2me | Theorems.Thm_SongZipkinFluct_Monotone_theorem2_b
-- name    : SongZipkinFluct.Monotone.theorem2_b
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-06T12:54:58.062954+00:00
-- url     : https://prove2.me/theorems/89b3bd1b-34c0-4b76-9f9e-e89988506cc9
-- title:
--   Theorem 2(b): $G_n\to G_\infty$ pointwise and $G_\infty(i,\cdot)$ has a smallest minimizer $y^*(i)$
-- statement:
--   Assume the standing hypotheses of the model and Assumption 1 ($\alpha\bar c<p$), in the linear-cost model ($K=0$, terminal cost $W_0\equiv 0$) with the recursion (13):
--   $$W_n(i,x)=\min_{y\ge x} G_n(i,y),\qquad G_n(i,y)=G^+(i,y)+\beta\lambda_i c+\beta\Big\{\lambda_i W_{n-1}(i,y-1)+\sum_{j\ne i}q_{ij}W_{n-1}(j,y)+(\mu-\lambda_i-q_i)W_{n-1}(i,y)\Big\}.$$
--   Let $G_\infty(i,y)=\sup_{n\ge1}G_n(i,y)$. Then
--
--   1. for every $i$ and $y$, $G_n(i,y)\to G_\infty(i,y)$ as $n\to\infty$ (so the supremum is a genuine limit), and
--   2. for every $i$, $G_\infty(i,\cdot)$ has a smallest minimizer $y^*(i)$ over $\mathbb Z$.
--
--   This is the part of Theorem 2(b) of the paper (p. 357) stating that $G_n$ converges to $G_\infty$, which is convex and coercive in $y$, so that its smallest minimizer $y^*(i)$ exists.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 357, Theorem 2(b) (with Theorem 1 (printed "Theorem 4") (d)–(e) giving monotone convergence)

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Recursion

open Filter Topology

namespace SongZipkinFluct.Monotone

theorem theorem2_b {I : Type} [Countable I] [Nonempty I] [DecidableEq I]
    (M : Model I) (hM : M.Standing) (hA : M.Assumption1) :
    (∀ (i : I) (y : ℤ),
      Tendsto (fun n : ℕ => M.Gn 0 0 (n + 1) i y) atTop (𝓝 (M.Ginf 0 0 i y))) ∧
    ∃ ystar : I → ℤ, ∀ i, IsSmallestMinimizer (M.Ginf 0 0 i) (ystar i) := by sorry

end SongZipkinFluct.Monotone
