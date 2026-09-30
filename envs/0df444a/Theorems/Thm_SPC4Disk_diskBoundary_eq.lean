-- Prove2me | Theorems.Thm_SPC4Disk_diskBoundary_eq
-- name    : SPC4Disk.diskBoundary_eq
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:35:10.644312+00:00
-- url     : https://prove2.me/theorems/acf72139-4a73-468f-8c25-338cccfa178e
-- title:
--   The manifold boundary of the explicit disk is the unit sphere
-- statement:
--   Let m be a nonnegative integer and let D be the closed unit ball in Euclidean (m+1)-space, with the explicit radial–stereographic atlas SPC4DiskCharts. Its manifold boundary is exactly
--
--   $$\partial D=\{z\in D:\|z\|=1\}.$$
--
--   This identifies the boundary defined by the half-space charts with the usual unit sphere as a subset of the ball. It is not a theorem about arbitrary boundaries or a smooth four-dimensional Poincaré claim.
-- source:
--   Unpublished archived Disk.lean, original lines 885–898; SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Declaration and proof ranges were extracted by the supplied Lean graph and sketch oracle.

import Mathlib
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem SPC4Disk.diskBoundary_eq :
    (𝓡∂ (m + 1)).boundary
      (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) =
      { z : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
        ‖z.val‖ = 1 } := by sorry
