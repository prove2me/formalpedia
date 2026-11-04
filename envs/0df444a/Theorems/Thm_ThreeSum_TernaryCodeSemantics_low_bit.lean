-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_low_bit
-- name    : ThreeSum.TernaryCodeSemantics.low_bit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:20:43.326079+00:00
-- url     : https://prove2.me/theorems/d72a492a-7790-4a92-ac4c-8cd9cabc91b3
-- title:
--   Ternary Code Semantics: low bit
-- statement:
--   The Ternary Code Semantics construction uses the low bit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L173-L182
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L173-L182

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.low_bit {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightMaskBits.bit (2*N) (address w) (low i)=if 0<(w i).val then 1 else 0 := by sorry
