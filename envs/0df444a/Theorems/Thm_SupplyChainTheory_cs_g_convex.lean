-- Prove2me | Theorems.Thm_SupplyChainTheory_cs_g_convex
-- name    : SupplyChainTheory.cs_g_convex
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:18:37.192356+00:00
-- url     : https://prove2.me/theorems/d4be37be-e415-4da8-8959-94d221316d6a
-- title:
--   Each $g_j$ of the Clark-Scarf recursion is convex under sequential minimization
-- statement:
--   For echelon holding costs $h_j \ge 0$, stockout cost $p \ge 0$, lead-time demands of finite
--   mean, and a base-stock vector $S$ built by the sequential minimization (6.26) (each $S_j$
--   minimizes $g_j(\cdot \mid S)$), every function $g_j(\cdot \mid S)$, $j \le N$, is convex on
--   $\mathbb{R}$.
--
--   This is the remark the book attaches to Theorem 6.3: at each iteration one minimizes a
--   single-variable convex function. The induction is that $\bar g_0$ is convex, $\hat g_j$ adds
--   a linear term to $\bar g_{j-1}$, $g_j$ is an expectation of translates of $\hat g_j$, and
--   $\bar g_j(x) = g_j(\min\{S_j, x\})$ is convex because $S_j$ is a minimizer of the convex
--   $g_j$: it is $g_j$ to the left of $S_j$ and constant to the right. The last step is where
--   sequential optimality is used; for an arbitrary $S$ the functions $\bar g_j$ need not be
--   convex.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 196, Sect. 6.2.2, the remark after Theorem 6.3: 'Moreover, gj(y) is known to be convex, so at each iteration we only need to minimize a single-variable, convex function'

import Definitions.Def_SupplyChainTheory_multiechelon

namespace SupplyChainTheory

theorem cs_g_convex (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ) (S : ℕ → ℝ)
    [∀ j, MeasureTheory.IsProbabilityMeasure (D j)]
    (hD : ∀ j, MeasureTheory.Integrable (fun x => x) (D j))
    (hh : ∀ j, 0 ≤ h j) (hp : 0 ≤ p) (hS : CSSequential N h p D S) (j : ℕ) (hj : j ≤ N) :
    ConvexOn ℝ Set.univ (csG N h p D S j) := by sorry

end SupplyChainTheory
