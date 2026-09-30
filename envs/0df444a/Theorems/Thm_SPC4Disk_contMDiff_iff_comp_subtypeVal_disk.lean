-- Prove2me | Theorems.Thm_SPC4Disk_contMDiff_iff_comp_subtypeVal_disk
-- name    : SPC4Disk.contMDiff_iff_comp_subtypeVal_disk
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-06T05:35:46.394462+00:00
-- url     : https://prove2.me/theorems/6240bc3f-c000-44a6-9c69-fed735a94b30
-- title:
--   Differentiability into the explicit disk through its ambient inclusion
-- statement:
--   Let m be a nonnegative integer and k any extended differentiability order. Let E be a real normed vector space, H a topological chart model, I a model with corners from H to E, and M a topological space charted over H that is a C^k manifold for I. For every function f from M to the closed unit ball D in real Euclidean (m+1)-space with the explicit disk atlas, f is C^k into D if and only if f is continuous and its composition with the subtype inclusion into Euclidean space is C^k. The continuity conjunct is retained exactly as stated, and the source IsManifold hypothesis is not omitted.
-- source:
--   Ryan Shin, unpublished Disk.lean, original lines 1260–1307; source SHA-256 889a9eccf9d2350aee7051ab7b6895e565f9f1a0c84e7120fb45c15acae0097e. Original declaration/proof ranges and reference edits come from the supplied Lean graph and sketch oracle; all four elaborated types (original, refactored, exact draft, solution) were compared.

import Mathlib
import Definitions.Def_SPC4DiskCharts

set_option autoImplicit false

open Set Metric SPC4Disk
open scoped ContDiff Manifold

noncomputable section
variable {m : ℕ}

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem SPC4Disk.contMDiff_iff_comp_subtypeVal_disk {k : ℕ∞ω}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I k M]
    {f : M → closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1} :
    ContMDiff I (𝓡∂ (m + 1)) k f ↔
      Continuous f ∧
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) k
          (fun a => (f a).val) := by sorry
