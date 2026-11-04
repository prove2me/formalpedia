-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorLayout_normalized_ends
-- name    : ThreeSum.EncodedColorLayout.normalized_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:34:24.92425+00:00
-- url     : https://prove2.me/theorems/e7038310-985d-43e8-a68e-002dc1909839
-- title:
--   Encoded Color Layout: normalized ends
-- statement:
--   The Encoded Color Layout construction uses the normalized ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorLayout.lean#L43-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorLayout.lean#L43-L51

import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorLayout

theorem ThreeSum.EncodedColorLayout.normalized_ends (free n g : ℕ) :
    av free n+n ≤ prime free n g ∧ ae free n+2+2*n ≤ prime free n g ∧
    bv free n+n ≤ prime free n g ∧ be free n+2+2*n ≤ prime free n g ∧
    cv free n+n ≤ prime free n g ∧ ce free n+2+2*n ≤ prime free n g ∧
    tables free n+ColorBandBounds.count n g ≤ prime free n g ∧
    rec free n g+4*ColorBandBounds.count n g ≤ prime free n g := by sorry
