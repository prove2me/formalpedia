-- Prove2me | Theorems.Thm_SPC4Disk_diskIsManifold
-- name    : SPC4Disk.diskIsManifold
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:34:54.512067+00:00
-- url     : https://prove2.me/theorems/8e6e87ad-648f-4f56-80fc-1d684bde4520
-- title:
--   The closed unit ball is a smooth manifold with boundary
-- statement:
--   Let m be a nonnegative integer and let D be the closed unit ball in Euclidean (m+1)-space. Equip D with the explicit atlas consisting of a translated interior chart and radial–stereographic boundary charts, as defined in SPC4DiskCharts. For every differentiability order k, this atlas makes D a C^k manifold modeled on the Euclidean half-space. In particular it gives a smooth manifold-with-boundary structure.
--
--   This verifies the chart-transition compatibility of a concrete atlas; it neither assumes that compatibility nor asserts any classification of other manifolds. The exact Lean type also covers the real-analytic order.
-- source:
--   Unpublished archived Disk.lean, original lines 719–848; SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Declaration and proof ranges were extracted by the supplied Lean graph and sketch oracle.

import Mathlib
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem SPC4Disk.diskIsManifold {k : ℕ∞ω} :
    IsManifold (𝓡∂ (m + 1)) k
      (closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) := by sorry
