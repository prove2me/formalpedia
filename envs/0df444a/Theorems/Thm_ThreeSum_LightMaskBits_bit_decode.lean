-- Prove2me | Theorems.Thm_ThreeSum_LightMaskBits_bit_decode
-- name    : ThreeSum.LightMaskBits.bit_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:46.927141+00:00
-- url     : https://prove2.me/theorems/43188c4f-ce66-425d-8ae9-d10c3dde7da5
-- title:
--   Light Mask Bits: bit decode
-- statement:
--   The Light Mask Bits construction uses the bit decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskBits.lean#L20-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightMaskBits.lean#L20-L22

import Definitions.Def_Submission_ThreeSum_LightMaskErase
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightMaskBits
set_option autoImplicit false
open ThreeSum ThreeSum.LightMaskBits
open Light LightSubsetAddress MaskErase

theorem ThreeSum.LightMaskBits.bit_decode {L m : ℕ} (hm : m < 2^L) (j : Fin L) :
    bit L m j.val = if j ∈ MaskDecode.decode L m then 1 else 0 := by sorry
