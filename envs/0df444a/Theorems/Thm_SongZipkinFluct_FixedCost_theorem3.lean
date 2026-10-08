-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_theorem3
-- name    : SongZipkinFluct.FixedCost.theorem3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:06.812894+00:00
-- url     : https://prove2.me/theorems/159e249e-3932-4c8b-9bd5-188fcc40c0cd
-- title:
--   Theorem 3 — G_n and W_n are K-convex and coercive, an (r, S) rule solves the n-stage problem, and W_n, G_n increase in n
-- statement:
--   Consider the fixed-cost model: the standing hypotheses, Assumption 1 ($\alpha\bar c < p$), $\bar K > 0$ (so $K = \bar K\tilde F_L(\alpha) > 0$), and the terminal cost $W_0 = W_\infty$ of the linear model. For any fixed $i$ and any $n \ge 1$:
--
--   1. $G_n(i, y)$ is $K$-convex as a function of $y$, and $\lim_{|y|\to\infty} G_n(i, y) = +\infty$;
--   2. the parameters $S^*_n(i)$ = the smallest global minimizer of $G_n(i, y)$ and $r^*_n(i)$ = the largest $y < S^*_n(i)$ with $G_n(i, y) > K + G_n(i, S^*_n(i))$ exist, and the $(r, S)$ rule with these parameters attains the minimum in (10): for every $x$, with $y = S^*_n(i)$ if $x \le r^*_n(i)$ and $y = x$ otherwise,
--   $$
--   W_n(i, x) = K\delta(y - x) + G_n(i, y);
--   $$
--   3. $W_n(i, x)$ is $K$-convex in $x$ and $\lim_{x\to+\infty} W_n(i, x) = +\infty$;
--   4. $W_n(i, x) \ge W_{n-1}(i, x) \ge 0$;
--   5. $G_{n+1}(i, y) \ge G_n(i, y) \ge 0$.
--
--   This is the finite-horizon structure theorem: an $(r, S)$ policy with world-dependent parameters is optimal for every $n$-stage problem, and the value iterates increase to the infinite-horizon limits.
--
--   **Formalization Note** $W_n$ is by definition the optimal $n$-stage cost (the recursion (10)), so "an optimal policy for the $n$-stage problem is an $(r, S)$ policy" is stated as: the $(r, S)$ decision attains the minimum defining $W_n(i, x)$ at every $x$. The existence of $S^*_n(i)$ and $r^*_n(i)$ is part of the conclusion.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 358, Theorem 3

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

open Filter Topology

namespace SongZipkinFluct.FixedCost

open Model

/-- Theorem 3 (p. 358) of Song and Zipkin (1993). Fixed-cost model of §3.2: `K = K̄F̃_L(α) > 0`
and terminal cost `W₀ = W_∞` of the linear model. For any fixed `i` and any `n ≥ 1`:

* (a) `G_n(i, ·)` is `K`-convex (Definition 2) and `G_n(i, y) → +∞` as `|y| → ∞`;
* (b) the `(r, S)` parameters exist (`S*_n(i)` the smallest global minimizer of `G_n(i, ·)`,
  `r*_n(i)` the largest `y < S*_n(i)` with `G_n(i, y) > K + G_n(i, S*_n(i))`), and the
  `(r, S)` rule with these parameters attains the minimum in (10) at every `x`;
* (c) `W_n(i, ·)` is `K`-convex and `W_n(i, x) → +∞` as `x → +∞`;
* (d) `W_n(i, x) ≥ W_{n−1}(i, x) ≥ 0`;
* (e) `G_{n+1}(i, y) ≥ G_n(i, y) ≥ 0`.

Formalization Note: `W_n` is the optimal `n`-stage cost by its definition through (10)
(p. 356), so "an optimal policy for the `n`-stage problem is an `(r, S)` policy" is encoded as:
the decision `y = S*_n(i)` if `x ≤ r*_n(i)`, `y = x` otherwise, attains the infimum defining
`W_n(i, x)`. Assumption 1 (`αc̄ < p`) is the paper's standing assumption from p. 356 on. -/
theorem theorem3 {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar) (i : I) (n : ℕ)
    (hn : 1 ≤ n) :
    (LConvex M.K (Gfix M n i) ∧ Tendsto (Gfix M n i) atTop atTop ∧
        Tendsto (Gfix M n i) atBot atTop) ∧
      ((∃ r S : ℤ, IsRSParams M.K (Gfix M n i) r S) ∧
        ∀ r S : ℤ, IsRSParams M.K (Gfix M n i) r S → ∀ x : ℤ,
          Wfix M n i x = M.K * SongZipkinFluct.Linear.delta ((if x ≤ r then S else x) - x)
            + Gfix M n i (if x ≤ r then S else x)) ∧
      (LConvex M.K (Wfix M n i) ∧ Tendsto (Wfix M n i) atTop atTop) ∧
      (∀ x : ℤ, Wfix M (n - 1) i x ≤ Wfix M n i x ∧ 0 ≤ Wfix M (n - 1) i x) ∧
      (∀ y : ℤ, Gfix M n i y ≤ Gfix M (n + 1) i y ∧ 0 ≤ Gfix M n i y) := by sorry

end SongZipkinFluct.FixedCost
