-- Prove2me | Theorems.Thm_SPC4Disk_contDiff_boundaryInv
-- name    : SPC4Disk.contDiff_boundaryInv
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:33:45.510486+00:00
-- url     : https://prove2.me/theorems/20ca9f88-0bfc-44f7-84f3-56b5d48f562c
-- title:
--   Smooth Euclidean extension of the inverse boundary chart
-- statement:
--   Let m be a nonnegative integer, p a point of the unit m-sphere, and k any differentiability order. Write u_p for the everywhere-defined inverse stereographic map used by the boundary chart centered in direction p. The Euclidean-coordinate map
--
--   $$y\longmapsto(1-y_0)u_p(y_1,\ldots,y_m)+2e_0$$
--
--   is C^k on all of Euclidean (m+1)-space. This is the unclamped extension of the boundary-to-interior transition formula, and is not a claim that the globally clamped chart inverse is everywhere smooth.
-- source:
--   Unpublished archived Disk.lean, original lines 547–577; SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Declaration and proof ranges were extracted by the supplied Lean graph and sketch oracle.

import Mathlib
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem SPC4Disk.contDiff_boundaryInv
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiff ℝ k (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
      (1 - y 0) • stereoInvFunAux
        (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
        (((OrthonormalBasis.fromOrthogonalSpanSingleton m
            (ne_zero_of_mem_unit_sphere (-p))).repr.symm
          (WithLp.toLp 2 (Fin.tail (fun i => y i)))) :
            EuclideanSpace ℝ (Fin (m + 1))) + diskShift (m + 1)) := by sorry
