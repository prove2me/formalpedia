-- Prove2me | Theorems.Thm_SongZipkinFluct_FixedCost_theorem5ab
-- name    : SongZipkinFluct.FixedCost.theorem5ab
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:57.950612+00:00
-- url     : https://prove2.me/theorems/beb834e6-3c2e-47c4-8783-dac4de5f0870
-- title:
--   Theorem 5(a), (b) — W_n → W_∞ and G_n → G_∞ pointwise; the limits are K-convex and coercive
-- statement:
--   In the fixed-cost model (standing hypotheses, $\alpha\bar c < p$, $K > 0$, $W_0 = W_\infty$ of the linear model), for every world state $i$:
--   1. the sequence $W_n(i, x)$ converges, for every $x$, to $W_\infty(i, x)$; $W_\infty(i, x)$ is $K$-convex in $x$ and $\lim_{x\to+\infty} W_\infty(i, x) = +\infty$;
--   2. the sequence $G_n(i, y)$ converges, for every $y$, to $G_\infty(i, y)$; $G_\infty(i, y)$ is $K$-convex in $y$ and $\lim_{|y|\to\infty} G_\infty(i, y) = +\infty$.
--
--   These are the limiting properties that carry the finite-horizon $(r, S)$ structure to the infinite horizon.
--
--   **Formalization Note** $W_\infty$ and $G_\infty$ are defined as suprema over $n$; the theorem asserts that the sequences converge to them.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 359, Theorem 5(a), (b)

import Mathlib
import Definitions.Def_SongZipkinFluct_FixedCost_Bounds

open Filter Topology

namespace SongZipkinFluct.FixedCost

open Model

/-- Theorem 5(a), (b) (p. 359) of Song and Zipkin (1993). Fixed-cost model of §3.2
(`K = K̄F̃_L(α) > 0`, `W₀ = W_∞` of the linear model). For all `i`:

* (a) `W_n(i, x)` converges, for every `x`, to `W_∞(i, x)`; `W_∞(i, ·)` is `K`-convex and
  `W_∞(i, x) → +∞` as `x → +∞`;
* (b) `G_n(i, y)` converges, for every `y`, to `G_∞(i, y)`; `G_∞(i, ·)` is `K`-convex and
  `G_∞(i, y) → +∞` as `|y| → ∞`.

Formalization Note: `W_∞` and `G_∞` are defined as the suprema over `n` (`WinfK`, `GinfK`); the
theorem asserts that the sequences converge to them. -/
theorem theorem5ab {I : Type*} [Countable I] [Nonempty I] [DecidableEq I] (M : Model I)
    (hM : M.Standing) (hA1 : M.α * M.cbar < M.p) (hK : 0 < M.Kbar) (i : I) :
    ((∀ x : ℤ, Tendsto (fun n => Wfix M n i x) atTop (𝓝 (WinfK M i x))) ∧
        LConvex M.K (WinfK M i) ∧ Tendsto (WinfK M i) atTop atTop) ∧
      ((∀ y : ℤ, Tendsto (fun n => Gfix M n i y) atTop (𝓝 (GinfK M i y))) ∧
        LConvex M.K (GinfK M i) ∧ Tendsto (GinfK M i) atTop atTop ∧
        Tendsto (GinfK M i) atBot atTop) := by sorry

end SongZipkinFluct.FixedCost
