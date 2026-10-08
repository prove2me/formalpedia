-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_lemma5
-- name    : SongZipkinFluct.FixedCost.lemma5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:12.765834+00:00
-- url     : https://prove2.me/theorems/d792ffff-0417-4ce4-b926-2ad87e8770af
-- title:
--   Lemma 5 — W_{n−1}(i, x + a) − W_{n−1}(i, x) ≥ −K and G_n(i, x + a) − G_n(i, x) ≥ G⁺(i, x + a) − G⁺(i, x) − γK
-- statement:
--   In the fixed-cost model (standing hypotheses, $\alpha\bar c < p$, $K > 0$, $W_0 = W_\infty$ of the linear model), for every world state $i$, every integer $x$, every integer $a > 0$ and every $n \ge 1$:
--   $$
--   W_{n-1}(i, x + a) - W_{n-1}(i, x) \ge -K,
--   $$
--   $$
--   G_n(i, x + a) - G_n(i, x) \ge G^+(i, x + a) - G^+(i, x) - \gamma K.
--   $$
--
--   These are the analogues of Lemma 1 of Veinott (1966): a $K$-convex value function can decrease by at most $K$, and the cost-to-go adds at most $\gamma K$ of non-convexity to the myopic cost $G^+$. They are the inputs of the upper bounds in Theorem 4.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 358, Lemma 5

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

open Filter Topology

namespace SongZipkinFluct.FixedCost

open Model

/-- Lemma 5 (p. 358) of Song and Zipkin (1993). Fixed-cost model of §3.2 (`K = K̄F̃_L(α) > 0`,
`W₀ = W_∞` of the linear model). For any integer `x`, any integer `a > 0` and `n ≥ 1`:

* (a) `W_{n−1}(i, x + a) − W_{n−1}(i, x) ≥ −K`;
* (b) `G_n(i, x + a) − G_n(i, x) ≥ G⁺(i, x + a) − G⁺(i, x) − γK`.

Formalization Note: the paper leaves `i` free; it is universally quantified. At `n = 1`
part (a) is about `W₀ = Wlin`. -/
theorem lemma5 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar) :
    ∀ n : ℕ, 1 ≤ n → ∀ (i : I) (x a : ℤ), 0 < a →
      -M.K ≤ Wfix M (n - 1) i (x + a) - Wfix M (n - 1) i x ∧
      M.Gplus i (x + a) - M.Gplus i x - M.γ * M.K ≤ Gfix M n i (x + a) - Gfix M n i x := by sorry

end SongZipkinFluct.FixedCost
