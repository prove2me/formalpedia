-- Prove2me | Theorems.Thm_SPC4Disk_range_diskCollar_mem_nhds
-- name    : SPC4Disk.range_diskCollar_mem_nhds
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:37:12.200967+00:00
-- url     : https://prove2.me/theorems/b397baf0-cea9-4795-bf4e-9b3d92574093
-- title:
--   The collar image is a neighborhood of every disk boundary point
-- statement:
--   For every nonnegative integer m and every point z of the closed unit ball D that lies in its manifold boundary for the explicit half-space atlas, the image of c(u,t)=(1−t/2)u belongs to the neighborhood filter of z in D. The neighborhood topology is the disk subtype topology, not the ambient Euclidean topology.
-- source:
--   Ryan Shin, unpublished Disk.lean, original lines 1130–1155; source SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Original declaration/proof ranges and reference edits come from the supplied Lean graph and sketch oracle; all four elaborated types (original, refactored, exact draft, solution) were compared.

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

theorem SPC4Disk.range_diskCollar_mem_nhds
    {z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1}
    (hz : z ∈ (𝓡∂ (m + 1)).boundary
      (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)) :
    Set.range (SPC4Disk.diskCollar (m := m)) ∈ nhds z := by sorry
