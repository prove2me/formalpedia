-- Prove2me | Theorems.Thm_ThreeSum_LightZetaPass_choose_le_cap
-- name    : ThreeSum.LightZetaPass.choose_le_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:52:20.374822+00:00
-- url     : https://prove2.me/theorems/9bf629ca-00dc-439d-9cd8-88f843b8bf0b
-- title:
--   Light Zeta Pass: choose le cap
-- statement:
--   The Light Zeta Pass construction uses the choose le cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaPass.lean#L25-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaPass.lean#L25-L30

import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightZetaPass
set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaPass
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaPass.choose_le_cap {L cut j : ℕ} (hcut : cut ≤ L) (hj : j ≤ cut) :
    L.choose j ≤ downsetCap L cut := by sorry
