-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorWantedData_header_le_nextFree
-- name    : ThreeSum.EncodedColorWantedData.header_le_nextFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:27:26.763194+00:00
-- url     : https://prove2.me/theorems/c0f430ff-cb63-4a04-bc0a-1630dbc5cac8
-- title:
--   Encoded Color Wanted Data: header le next Free
-- statement:
--   The Encoded Color Wanted Data construction uses the header le next Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedData.lean#L12-L16
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedData.lean#L12-L16

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedData
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedData
open Light WantedResidueKeys

theorem ThreeSum.EncodedColorWantedData.header_le_nextFree (out M : ℕ) (left right : ℕ → ℤ) (NL NR : ℕ) (shift : ℤ) :
    out+4 ≤ nextFree out M left right NL NR shift := by sorry
