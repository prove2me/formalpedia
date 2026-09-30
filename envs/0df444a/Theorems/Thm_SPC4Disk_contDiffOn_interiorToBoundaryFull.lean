-- Prove2me | Theorems.Thm_SPC4Disk_contDiffOn_interiorToBoundaryFull
-- name    : SPC4Disk.contDiffOn_interiorToBoundaryFull
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:34:37.000495+00:00
-- url     : https://prove2.me/theorems/f544eb10-cd03-4eba-8eb6-41655fde49b7
-- title:
--   Smooth transition from the translated interior chart to a boundary chart
-- statement:
--   Let m be a nonnegative integer, p a unit-sphere direction, and k any differentiability order. After translating v by −2e₀, form its radial coordinate 1−‖v−2e₀‖ and its stereographic angular coordinates in the p-boundary chart. This Euclidean map is C^k where v−2e₀ is nonzero and the normalized vector has inner product different from 1 with −p.
--
--   The two exclusions are the origin and the stereographic pole. The statement concerns the explicit transition formula on this domain, not a global smoothness claim for normalization at the origin.
-- source:
--   Unpublished archived Disk.lean, original lines 670–709; SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Declaration and proof ranges were extracted by the supplied Lean graph and sketch oracle.

import Mathlib
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem SPC4Disk.contDiffOn_interiorToBoundaryFull
    (p : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) {k : ℕ∞ω} :
    ContDiffOn ℝ k
      (fun v : EuclideanSpace ℝ (Fin (m + 1)) =>
        (WithLp.toLp 2 (Fin.cons (1 - ‖v - diskShift (m + 1)‖)
          (fun i => ((OrthonormalBasis.fromOrthogonalSpanSingleton m
              (ne_zero_of_mem_unit_sphere (-p))).repr
            (stereoToFun (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
                EuclideanSpace ℝ (Fin (m + 1)))
              (‖v - diskShift (m + 1)‖⁻¹ • (v - diskShift (m + 1))))) i)) :
          EuclideanSpace ℝ (Fin (m + 1))))
      { v : EuclideanSpace ℝ (Fin (m + 1)) | v - diskShift (m + 1) ≠ 0 ∧
        innerSL ℝ (((-p) : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
          EuclideanSpace ℝ (Fin (m + 1)))
          (‖v - diskShift (m + 1)‖⁻¹ • (v - diskShift (m + 1))) ≠ (1 : ℝ) } := by sorry
