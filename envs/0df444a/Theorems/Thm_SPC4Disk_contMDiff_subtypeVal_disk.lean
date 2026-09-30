-- Prove2me | Theorems.Thm_SPC4Disk_contMDiff_subtypeVal_disk
-- name    : SPC4Disk.contMDiff_subtypeVal_disk
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:35:28.899929+00:00
-- url     : https://prove2.me/theorems/1d7dc93f-120c-4ceb-b985-a2a2b758e417
-- title:
--   The inclusion of the explicit closed disk is differentiable to every order
-- statement:
--   Let m be any nonnegative integer and D the closed unit ball in real Euclidean (m+1)-space, with the explicit radial–stereographic atlas SPC4DiskCharts. For every extended differentiability order k (finite, smooth, or analytic), the subtype inclusion D → ℝ^(m+1) is C^k as a manifold map from the half-space model to the ambient vector-space model. No additional dimension or pointwise hypothesis is imposed.
-- source:
--   Ryan Shin, unpublished Disk.lean, original lines 1173–1216; source SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Original declaration/proof ranges and reference edits come from the supplied Lean graph and sketch oracle; all four elaborated types (original, refactored, exact draft, solution) were compared.

import Mathlib
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem SPC4Disk.contMDiff_subtypeVal_disk {k : ℕ∞ω} :
    ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) k
      (Subtype.val : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 →
        EuclideanSpace ℝ (Fin (m + 1))) := by sorry
