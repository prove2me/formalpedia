-- Prove2me | Theorems.Thm_TateCurve_hasSum_yfun
-- name    : TateCurve.hasSum_yfun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/2c7a8a6e-240d-59b5-812e-5e7aef428f04
-- title:
--   Power series expansion of w²/(1-w)³
-- statement:
--   Let $K$ be a nontrivially normed field whose distance is ultrametric, and let $w \in K$ satisfy $\|w\|_{\mathbb{R}_{\ge 0}} < 1$, i.e. the non-negative real number $\|w\|$ is strictly less than $1$. The assertion is that the family indexed by $m \in \mathbb{N}$ whose $m$-th term is the image in $K$ of the binomial coefficient $\binom{m+2}{2}$ multiplied by $w^{m+2}$ is summable with sum `yfun w`, which by definition is the element $w^2/(1-w)^3$ of $K$. Thus, reindexing, the series $\sum_{n \ge 2} \binom{n}{2} w^n$ converges unconditionally in $K$ to $w^2/(1-w)^3$ whenever $\|w\| < 1$. The conclusion is phrased as `HasSum`, so it records both summability of the family and the identification of its sum, for the unordered sum over $\mathbb{N}$.
--
--   This is the $Y$-coordinate companion of the elementary geometric-type expansion used in the Tate curve: `yfun` is the rational function occurring in the coefficient series for the $Y$-coordinate of points on the Tate parametrisation. It is cited by [`TateCurve.pointX_qExpansion`](thm.html#TateCurve.pointX_qExpansion) and [`TateCurve.pointY_qExpansion`](thm.html#TateCurve.pointY_qExpansion), where the $q$-expansions of the coordinate functions are assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_hasSum_yfun.lean

import Definitions.Def_TateCurve_PointSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TateCurve
open scoped NNReal

theorem TateCurve.hasSum_yfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw : ‖w‖₊ < 1) : HasSum (fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2)) (yfun w) := by sorry
