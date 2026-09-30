-- Prove2me | Theorems.Thm_SPC4Disk_range_diskCollar
-- name    : SPC4Disk.range_diskCollar
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:36:32.02015+00:00
-- url     : https://prove2.me/theorems/7d7e5234-156b-405d-ae8f-73dca1a72c51
-- title:
--   The exact image of the radial disk collar
-- statement:
--   For every nonnegative integer m, the image of c(u,t)=(1−t/2)u from the unit m-sphere times the closed interval [0,1] into the closed unit ball D is exactly the subset of D consisting of points of norm at least 1/2. Both radii 1/2 and 1 are included; the upper bound comes from membership in D.
-- source:
--   Ryan Shin, unpublished Disk.lean, original lines 1081–1106; source SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Original declaration/proof ranges and reference edits come from the supplied Lean graph and sketch oracle; all four elaborated types (original, refactored, exact draft, solution) were compared.

import Mathlib
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SPC4DiskCollar

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem SPC4Disk.range_diskCollar :
    Set.range (SPC4Disk.diskCollar (m := m)) =
      { z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
        1 / 2 ≤ ‖z.val‖ } := by sorry
