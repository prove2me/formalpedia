-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_entries_complete
-- name    : ThreeSum.LightTernaryRequesterMatrix.entries_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:01:18.736923+00:00
-- url     : https://prove2.me/theorems/075b3eaf-0031-4df0-897b-d061eb5a86d1
-- title:
--   Light Ternary Requester Matrix: entries complete
-- statement:
--   Every valid carry and original position has its literal emitted row.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L243-L259
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L243-L259

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {depth : ℕ}

theorem ThreeSum.LightTernaryRequesterMatrix.entries_complete {μ : ℕ → ℤ} {positions matrix J n U radix : ℕ} {f : ℕ → ℤ}
    (H : Entries μ positions matrix J (2^J) (n*2^J) U radix f)
    {i : ℕ} (hi : i<n) (c : CarryWord J) (hc : ValidCarry c) :
    ∃r<n*2^J, LightTernarySignedRow.Row μ (matrix+r*(J+2)) J (requesterRaw U radix J (f i) c) ∧
      μ (positions+r)=(i : ℤ) := by sorry
