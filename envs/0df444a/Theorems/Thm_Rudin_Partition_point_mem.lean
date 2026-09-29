-- Prove2me | Theorems.Thm_Rudin_Partition_point_mem
-- name    : Rudin.Partition.point_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T00:02:45.274985+00:00
-- url     : https://prove2.me/theorems/1aec92a1-678d-4119-a1da-8f3f5d1aa1f6
-- title:
--   Every division point lies in the partition interval
-- statement:
--   For a partition $P=(x_0,\ldots,x_n)$ of $[a,b]$, every division point with index $0\le i\le n$ belongs to the interval:
--
--   $$a\le x_i\le b.$$
--
--   This packages the repeated use of adjacent monotonicity into a reusable interface for arguments about Riemann–Stieltjes sums.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Definition 6.1 (partition of an interval).

import Definitions.Def_Rudin_ch06_stieltjes

namespace Rudin

theorem Partition.point_mem {a b : ℝ} (P : Partition a b) {i : ℕ}
    (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by sorry
