-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_succ_one
-- name    : ThreeSum.LightTernaryEnumeration.output_succ_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:37.968582+00:00
-- url     : https://prove2.me/theorems/1814fa95-5cbc-48cb-a414-8a0a5c603dcc
-- title:
--   Light Ternary Enumeration: output succ one
-- statement:
--   The Light Ternary Enumeration construction uses the output succ one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L31-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L31-L34

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEnumeration.output_succ_one (N pref : ℕ) :
    output (N+1) 1 pref = output N 1 pref ++ output N 0 (pref+4^N) := by sorry
