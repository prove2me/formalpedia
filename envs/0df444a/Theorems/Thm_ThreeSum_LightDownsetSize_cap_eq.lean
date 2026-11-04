-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetSize_cap_eq
-- name    : ThreeSum.LightDownsetSize.cap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:16:46.004135+00:00
-- url     : https://prove2.me/theorems/1acc8084-fe62-49c7-b572-9a5c6f85b2f2
-- title:
--   Light Downset Size: cap eq
-- statement:
--   The Light Downset Size construction uses the cap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean#L26-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetSize.lean#L26-L28

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetSize
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetSize.cap_eq {L cut : ℕ} (hcut : cut ≤ L) :
    downsetCap L cut = layerOffset L cut+L.choose cut := by sorry
