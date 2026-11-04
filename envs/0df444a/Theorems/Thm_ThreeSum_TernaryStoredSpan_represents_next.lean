-- Prove2me | Theorems.Thm_ThreeSum_TernaryStoredSpan_represents_next
-- name    : ThreeSum.TernaryStoredSpan.represents_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:21.361268+00:00
-- url     : https://prove2.me/theorems/6ab71778-4718-4dc9-86d6-c0c2dac931e7
-- title:
--   Ternary Stored Span: represents next
-- statement:
--   The Ternary Stored Span construction uses the represents next property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryStoredSpan.lean#L38-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryStoredSpan.lean#L38-L73

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryStoredSpan
open ThreeSum
set_option maxHeartbeats 3000000
variable {p J n : ℕ}

theorem ThreeSum.TernaryStoredSpan.represents_next [Fact p.Prime] (f : ℕ → ℕ → ℕ) (row : Fin J → ZMod p)
    (rows : List (Fin J → ZMod p)) (hn : 0<n) (H : Represents f n rows) :
    Represents (next f (fun i => if hi : i<J then (row ⟨i,hi⟩).val else 0) p n) (p*n) (row::rows) := by sorry
