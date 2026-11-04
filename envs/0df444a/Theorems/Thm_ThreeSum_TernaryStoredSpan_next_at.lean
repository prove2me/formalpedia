-- Prove2me | Theorems.Thm_ThreeSum_TernaryStoredSpan_next_at
-- name    : ThreeSum.TernaryStoredSpan.next_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:12.350788+00:00
-- url     : https://prove2.me/theorems/54445c49-16d2-4956-a8d3-1fb9be6bdbf9
-- title:
--   Ternary Stored Span: next at
-- statement:
--   The Ternary Stored Span construction uses the next at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryStoredSpan.lean#L31-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryStoredSpan.lean#L31-L36

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryStoredSpan
open ThreeSum
set_option maxHeartbeats 3000000
variable {p J n : ℕ}

theorem ThreeSum.TernaryStoredSpan.next_at (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ) (hp : 0<n) {a k : ℕ} (hk : k<n) (i : ℕ) :
    next f row p n (a*n+k) i=(f k i+a*row i)%p := by sorry
