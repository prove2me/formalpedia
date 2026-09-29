-- Prove2me | Theorems.Thm_Rudin_exists_partition
-- name    : Rudin.exists_partition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T00:02:52.630981+00:00
-- url     : https://prove2.me/theorems/146b8982-54bf-47cd-9d47-da7860f97c15
-- title:
--   A nondegenerate ordered interval admits a partition
-- statement:
--   Every ordered closed interval $[a,b]$ with $a\le b$ has a partition. Explicitly, the two endpoints form a one-subinterval partition.
--
--   This guarantees that the families of upper and lower Darboux sums are nonempty, which is needed when comparing their infimum and supremum.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Definition 6.1 (partition of an interval).

import Definitions.Def_Rudin_ch06_stieltjes

namespace Rudin

theorem exists_partition {a b : ℝ} (hab : a ≤ b) :
    Nonempty (Partition a b) := by sorry
