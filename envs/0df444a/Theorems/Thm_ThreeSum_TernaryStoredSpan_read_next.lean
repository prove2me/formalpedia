-- Prove2me | Theorems.Thm_ThreeSum_TernaryStoredSpan_read_next
-- name    : ThreeSum.TernaryStoredSpan.read_next
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:39.09712+00:00
-- url     : https://prove2.me/theorems/7d011a46-313d-48a2-b64a-854963ff88cf
-- title:
--   Ternary Stored Span: read next
-- statement:
--   The actual coefficient/old-row nested output is the complete next matrix.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryStoredSpan.lean#L76-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryStoredSpan.lean#L76-L88

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest
import Definitions.Def_Submission_ThreeSum_TernaryStoredSpan
import Theorems.Thm_Light_Ends_next

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryStoredSpan
open ThreeSum
set_option maxHeartbeats 3000000
variable {p J n : ℕ}

theorem ThreeSum.TernaryStoredSpan.read_next {μ : ℕ → ℤ} {src J p n : ℕ} (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ) (hn : 0<n)
    (H : ∀ a<p, ∀ k<n, ∀ i<J, μ (src+J*n*a+J*k+i)=LightSpanAxpy.values (f k) row a p i) :
    ∀ q<p*n, ∀ i<J, μ (src+J*q+i)=(next f row p n q i : ℤ) := by sorry
