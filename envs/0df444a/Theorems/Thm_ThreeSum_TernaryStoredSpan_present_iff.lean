-- Prove2me | Theorems.Thm_ThreeSum_TernaryStoredSpan_present_iff
-- name    : ThreeSum.TernaryStoredSpan.present_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:17.645774+00:00
-- url     : https://prove2.me/theorems/b7d9eb2f-e831-4e45-a7cf-c55f0c63a804
-- title:
--   Ternary Stored Span: present iff
-- statement:
--   Exact digit-restriction admissibility follows from actual coordinate
--   comparisons and the established physical catalog invariant.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryStoredSpan.lean#L92-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryStoredSpan.lean#L92-L112

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryStoredSpan
open ThreeSum
set_option maxHeartbeats 3000000
variable {p J n : ℕ}

theorem ThreeSum.TernaryStoredSpan.present_iff [Fact p.Prime] (f : ℕ → ℕ → ℕ) (n : ℕ)
    (rows : List (Fin J → ZMod p)) (row : Fin J → ZMod p)
    (H : Represents f n rows) (hf : ∀ k<n, ∀ i<J, f k i<p) :
    LightSpanCatalogTest.Present (fun k i => (f k i : ℤ))
      (fun i => if hi : i<J then ((row ⟨i,hi⟩).val : ℤ) else 0) J n ↔
      row∈Submodule.span (ZMod p) {v | v∈rows} := by sorry
