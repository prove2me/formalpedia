-- Prove2me | Theorems.Thm_SPC4Disk_contMDiff_diskCollar
-- name    : SPC4Disk.contMDiff_diskCollar
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:37:32.811001+00:00
-- url     : https://prove2.me/theorems/e1a9f60b-ee68-4f03-a411-e699529fd84b
-- title:
--   The explicit radial collar is smooth into the disk manifold
-- statement:
--   For every nonnegative integer m, the explicit map c(u,t)=(1−t/2)u from the unit m-sphere times the closed interval [0,1] to the closed unit ball is smooth. The source uses the product of the usual sphere model and the interval half-space model; the target uses the concrete SPC4DiskCharts half-space atlas. This theorem asserts C^∞ smoothness of this specified map and does not assert an arbitrary-manifold collar or an independently defined annulus smooth structure.
-- source:
--   Ryan Shin, unpublished Disk.lean, original lines 1310–1319; source SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Original declaration/proof ranges and reference edits come from the supplied Lean graph and sketch oracle; all four elaborated types (original, refactored, exact draft, solution) were compared.

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

theorem SPC4Disk.contMDiff_diskCollar :
    ContMDiff ((𝓡 m).prod (𝓡∂ 1)) (𝓡∂ (m + 1)) ∞ (SPC4Disk.diskCollar (m := m)) := by sorry
