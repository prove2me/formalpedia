-- Prove2me | Theorems.Thm_SPC4Disk_contDiffOn_boundaryToBoundary
-- name    : SPC4Disk.contDiffOn_boundaryToBoundary
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:34:12.779629+00:00
-- url     : https://prove2.me/theorems/efd0c19f-332d-41ea-88fb-3b2b9ac58a32
-- title:
--   Smooth transition between radial–stereographic boundary charts
-- statement:
--   Let m be a nonnegative integer, p and p′ points of the unit m-sphere, and k any differentiability order. The change of boundary coordinates keeps the first, radial coordinate and applies the sphere’s stereographic change of angular coordinates to the remaining coordinates. Its Euclidean extension is C^k on the set where the inner product of −p′ with the inverse-stereographic unit vector from the p-chart is not 1.
--
--   The domain explicitly excludes the second projection’s pole. This is the analytic compatibility result used in the disk atlas assembly.
-- source:
--   Unpublished archived Disk.lean, original lines 603–668; SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Declaration and proof ranges were extracted by the supplied Lean graph and sketch oracle.

import Mathlib
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem SPC4Disk.contDiffOn_boundaryToBoundary
    (p p' : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiffOn ℝ k
      (fun y : EuclideanSpace ℝ (Fin (m + 1)) =>
        (WithLp.toLp 2 (Fin.cons (y 0)
          (fun i => ((OrthonormalBasis.fromOrthogonalSpanSingleton m
              (ne_zero_of_mem_unit_sphere (-p'))).repr
            (stereoToFun (((-p') : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                EuclideanSpace ℝ (Fin (m + 1)))
              (stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                  EuclideanSpace ℝ (Fin (m + 1)))
                (((OrthonormalBasis.fromOrthogonalSpanSingleton m
                    (ne_zero_of_mem_unit_sphere (-p))).repr.symm
                  (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
                    EuclideanSpace ℝ (Fin (m + 1)))))) i)) :
          EuclideanSpace ℝ (Fin (m + 1))))
      { y : EuclideanSpace ℝ (Fin (m + 1)) |
        innerSL ℝ (((-p') : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
            EuclideanSpace ℝ (Fin (m + 1)))
          (stereoInvFunAux (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
              EuclideanSpace ℝ (Fin (m + 1)))
            (((OrthonormalBasis.fromOrthogonalSpanSingleton m
                (ne_zero_of_mem_unit_sphere (-p))).repr.symm
              (WithLp.toLp 2 (Fin.tail (fun j => y j)))) :
                EuclideanSpace ℝ (Fin (m + 1)))) ≠ (1 : ℝ) } := by sorry
