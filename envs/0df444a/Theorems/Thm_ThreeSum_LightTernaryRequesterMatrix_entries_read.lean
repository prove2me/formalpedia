-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryRequesterMatrix_entries_read
-- name    : ThreeSum.LightTernaryRequesterMatrix.entries_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:59.715364+00:00
-- url     : https://prove2.me/theorems/8868eeba-230d-4019-bed5-76b5459e898d
-- title:
--   Light Ternary Requester Matrix: entries read
-- statement:
--   The Light Ternary Requester Matrix construction uses the entries read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L295-L302
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryRequesterMatrix.lean#L295-L302

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

theorem ThreeSum.LightTernaryRequesterMatrix.entries_read {μ : ℕ → ℤ} {positions matrix J Q len U radix : ℕ} {f : ℕ → ℤ}
    (H : Entries μ positions matrix J Q len U radix f) :
    (∀row<len, ∀coordinate<J+2,
      μ (matrix+row*(J+2)+coordinate)=value U radix J Q f row coordinate) ∧
      (∀row<len, μ (positions+row)=(row/Q : ℕ)) := by sorry
