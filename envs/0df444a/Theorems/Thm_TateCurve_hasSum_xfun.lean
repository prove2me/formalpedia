-- Prove2me | Theorems.Thm_TateCurve_hasSum_xfun
-- name    : TateCurve.hasSum_xfun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/d1d5314d-7bc6-51b4-bf2d-a7fe4d7756f7
-- title:
--   Geometric series for w/(1-w)² over an ultrametric field
-- statement:
--   Let $K$ be a nontrivially normed field whose distance is ultrametric, and let $w \in K$ satisfy $\|w\|_+ < 1$ (the bound being stated for the nonnegative-real-valued norm). The assertion is that the family indexed by $m \in \mathbb{N}$ whose $m$-th term is $((m+1) : K) \cdot w^{m+1}$, where $m+1$ is taken as a natural number and then mapped into $K$, is summable with sum `xfun w`, i.e. with sum $w/(1-w)^2$, that being precisely the definition of `xfun` in the project. In other words, $\sum_{m \ge 0} (m+1) w^{m+1} = \sum_{n \ge 1} n w^n$ converges unconditionally in $K$ to $w/(1-w)^2$. The conclusion is phrased as `HasSum`, so it records both the summability of the family and the identification of its sum, and the index set is all of $\mathbb{N}$ with the $m = 0$ term equal to $w$.
--
--   This is the generating-function identity $\sum_{n \ge 1} n w^n = w/(1-w)^2$ in the non-archimedean setting; $w/(1-w)^2$ is the building block of the coordinate functions of the Tate parametrisation, playing over $K$ the role that the corresponding term of the $q$-expansion of the Weierstrass $\wp$-function plays over $\mathbb{C}$. It is used in the $q$-expansions of the Tate curve coordinates, [`TateCurve.pointX_qExpansion`](thm.html#TateCurve.pointX_qExpansion) and [`TateCurve.pointY_qExpansion`](thm.html#TateCurve.pointY_qExpansion), and in [`TateCurve.sOne_eq_tsum_xfun`](thm.html#TateCurve.sOne_eq_tsum_xfun).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_hasSum_xfun.lean

import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve
open scoped NNReal

theorem TateCurve.hasSum_xfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw : ‖w‖₊ < 1) : HasSum (fun m : ℕ => ((m + 1 : ℕ) : K) * w ^ (m + 1)) (xfun w) := by sorry
