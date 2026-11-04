-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_high_bit
-- name    : ThreeSum.TernaryCodeSemantics.high_bit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:49.124616+00:00
-- url     : https://prove2.me/theorems/bc3c01b2-ec0f-4c3a-95f9-d5381c96232f
-- title:
--   Ternary Code Semantics: high bit
-- statement:
--   The Ternary Code Semantics construction uses the high bit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L184-L193
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L184-L193

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_high

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.high_bit {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightMaskBits.bit (2*N) (address w) (high i)=if w i=2 then 1 else 0 := by sorry
