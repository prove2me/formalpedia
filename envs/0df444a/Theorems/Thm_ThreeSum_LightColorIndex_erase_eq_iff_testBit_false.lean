-- Prove2me | Theorems.Thm_ThreeSum_LightColorIndex_erase_eq_iff_testBit_false
-- name    : ThreeSum.LightColorIndex.erase_eq_iff_testBit_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:09:51.39657+00:00
-- url     : https://prove2.me/theorems/55b91117-3144-4966-ba56-3e923cb1bf35
-- title:
--   Light Color Index: erase eq iff test Bit false
-- statement:
--   The Light Color Index construction uses the erase eq iff test Bit false property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorIndex.lean#L20-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightColorIndex.lean#L20-L26

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_LightColorIndex
set_option autoImplicit false
open ThreeSum ThreeSum.LightColorIndex
open Light LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightColorIndex.erase_eq_iff_testBit_false {W m : ℕ} (hm : m < 2^W) (i : Fin W) :
    MaskErase.eraseMask W i.val m = m ↔ m.testBit i.val = false := by sorry
