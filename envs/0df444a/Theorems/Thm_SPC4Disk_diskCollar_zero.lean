-- Prove2me | Theorems.Thm_SPC4Disk_diskCollar_zero
-- name    : SPC4Disk.diskCollar_zero
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:36:52.774974+00:00
-- url     : https://prove2.me/theorems/1b23a262-4e76-4213-8bab-804f93647a5b
-- title:
--   The zero section of the radial collar is the boundary inclusion
-- statement:
--   For every nonnegative integer m and every point u of the unit m-sphere, evaluating the explicit collar at (u,0) equals the underlying disk point of the inverse image of u under SPC4Disk.diskBoundaryHomeoSphere. That homeomorphism identifies the boundary determined by the explicit disk charts with the unit sphere, without moving the ambient point. The assertion preserves the specific boundary-identification map, not merely the existence of some boundary parametrization.
-- source:
--   Ryan Shin, unpublished Disk.lean, original lines 1120–1127; source SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Original declaration/proof ranges and reference edits come from the supplied Lean graph and sketch oracle; all four elaborated types (original, refactored, exact draft, solution) were compared.

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

theorem SPC4Disk.diskCollar_zero (u : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    SPC4Disk.diskCollar (u, ⟨0, by norm_num⟩) =
      ((SPC4Disk.diskBoundaryHomeoSphere (m := m)).symm u).val := by sorry
