-- Prove2me | Theorems.Thm_ThreeSum_TernaryCodeSemantics_bit_maskOf
-- name    : ThreeSum.TernaryCodeSemantics.bit_maskOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:56:12.485347+00:00
-- url     : https://prove2.me/theorems/046817fc-f7b6-47fa-9043-5f8ff119c687
-- title:
--   Ternary Code Semantics: bit mask Of
-- statement:
--   The Ternary Code Semantics construction uses the bit mask Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L160-L171
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCodeSemantics.lean#L160-L171

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryCodeSemantics.bit_maskOf {W : ℕ} (s : Finset ℕ) (hs : s ⊆ range W) (a : ℕ) :
    LightMaskBits.bit W (maskOf s) a=if a∈s then 1 else 0 := by sorry
