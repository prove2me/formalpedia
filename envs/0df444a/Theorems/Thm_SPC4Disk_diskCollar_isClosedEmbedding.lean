-- Prove2me | Theorems.Thm_SPC4Disk_diskCollar_isClosedEmbedding
-- name    : SPC4Disk.diskCollar_isClosedEmbedding
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:36:08.291737+00:00
-- url     : https://prove2.me/theorems/8c54405c-e7cf-4789-bd01-88af393d1762
-- title:
--   The explicit radial disk collar is a closed embedding
-- statement:
--   For every nonnegative integer m, let D be the closed unit ball in real Euclidean (m+1)-space, S its unit sphere, and c : S × [0,1] → D the map c(u,t)=(1−t/2)u. Then c is a closed topological embedding. The interval includes both endpoints, and m=0 is included. This is the stated explicit disk map, not a collar theorem for arbitrary manifolds.
-- source:
--   Ryan Shin, unpublished Disk.lean, original lines 1074–1078; source SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Original declaration/proof ranges and reference edits come from the supplied Lean graph and sketch oracle; all four elaborated types (original, refactored, exact draft, solution) were compared.

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

theorem SPC4Disk.diskCollar_isClosedEmbedding :
    Topology.IsClosedEmbedding (SPC4Disk.diskCollar (m := m)) := by sorry
