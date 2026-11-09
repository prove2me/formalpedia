-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_almost_spanning_cycle
-- name    : ThinningSprinkling306.ToughCycles.almost_spanning_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:11.517422+00:00
-- url     : https://prove2.me/theorems/9e373db1-3106-4c88-96fc-fecf1484b87c
-- title:
--   Theorem 1.6 — almost spanning cycles in polylogarithmically tough graphs
-- statement:
--   Let $n_j$ be any sequence of natural numbers tending to infinity. Let $G_j$ be arbitrary finite simple undirected graphs on $n_j$ vertices, and let $t_j$ be real parameters such that $G_j$ is eventually $t_j$-tough and
--   $$
--   \frac{t_j}{(\log n_j)^3}\longrightarrow+\infty.
--   $$
--   Then for every real $\delta>0$, eventually there is a simple cycle $C$ in $G_j$ with
--   $$
--   |V(C)|\ge(1-\delta)n_j.
--   $$
--   The size of a simple cycle equals its edge length. The family may have arbitrary sizes, subsequences, divergence rates and irregular graphs, including complete graphs. No successful partition, matching, forest, regularity condition or fixed loss is assumed. This is the full almost-Hamiltonicity conclusion of the source.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - encoding: asymptotics as the vertex count n tends to infinity → every sequence of sizes n_j tending to infinity, with real ratios tending to positive infinity and eventual conclusions; reason: arbitrary sizes, subsequences and divergence rates are retained; finite initial terms do not affect the result
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 4, Theorem 1.6 (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Paths
open Filter

namespace ThinningSprinkling306.ToughCycles

/-- Theorem 1.6, printed p. 4 (PDF p. 6), at its full asymptotic strength. -/
theorem almost_spanning_cycle (n : ℕ → ℕ)
    (G : (j : ℕ) → SimpleGraph (Fin (n j))) (t : ℕ → ℝ)
    (hn : Tendsto n atTop atTop)
    (hG : ∀ᶠ j in atTop, Tough (G j) (t j))
    (ht : Tendsto (fun j => t j / (Real.log (n j : ℝ)) ^ 3) atTop atTop) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ j in atTop,
      LongCycle (G j) ((1 - δ) * (n j : ℝ)) := by sorry

end ThinningSprinkling306.ToughCycles
