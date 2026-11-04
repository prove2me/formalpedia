-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorWantedData_nextFree_read
-- name    : ThreeSum.EncodedColorWantedData.nextFree_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:26:15.603873+00:00
-- url     : https://prove2.me/theorems/82d8ae6a-7fa3-49c0-92f3-414b50d3b5d1
-- title:
--   Encoded Color Wanted Data: next Free read
-- statement:
--   The Encoded Color Wanted Data construction uses the next Free read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedData.lean#L18-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorWantedData.lean#L18-L20

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_EncodedColorWantedData
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorWantedData
open Light WantedResidueKeys

theorem ThreeSum.EncodedColorWantedData.nextFree_read {μ : ℕ → ℤ} {out M NL NR : ℕ} {left right : ℕ → ℤ} {shift : ℤ}
    (H : LightWantedSetup.Output μ out M left right NL NR shift) :
    μ (out+2)=(nextFree out M left right NL NR shift : ℤ) := by sorry
