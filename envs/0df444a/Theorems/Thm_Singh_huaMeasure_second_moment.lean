-- Prove2me | Theorems.Thm_Singh_huaMeasure_second_moment
-- name    : Singh.huaMeasure_second_moment
-- status  : Proved
-- author  : @Hix_Lab
-- created : 2026-11-04T06:04:38.334971+00:00
-- url     : https://prove2.me/theorems/349565f6-6138-4cb9-8e83-01ffed05c3fd
-- title:
--   Hua second moment: $E_{n,2}\left[(\sum_k u_k)^2\right] = \frac{n(n+4)}{15}$
-- statement:
--   For every $n \ge 0$, let $P_{n,2}$ be the probability measure on $\mathbb{R}^n$ with density proportional to $\prod_{j<k}(u_j-u_k)^2\prod_k(1+u_k^2)^{-(n+2)}$ (`huaMeasure n`). Then
--   $$\int \Big(\sum_{k=1}^n u_k\Big)^2 \, dP_{n,2}(u) = \frac{n(n+4)}{15}.$$
-- source:
--   J. Singh, https://github.com/jjsingh88/singh-constant (commit 792d985)

import Mathlib
import Definitions.Def_Singh

open MeasureTheory Filter Topology

namespace Singh

theorem huaMeasure_second_moment (n : ℕ) :
    ∫ u, (∑ k, u k) ^ 2 ∂(huaMeasure n) = (n : ℝ) * ((n : ℝ) + 4) / 15 := by sorry

end Singh
