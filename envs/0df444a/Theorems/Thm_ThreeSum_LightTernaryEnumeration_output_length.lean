-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
-- name    : ThreeSum.LightTernaryEnumeration.output_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:35:30.471087+00:00
-- url     : https://prove2.me/theorems/958f6ee9-ae7b-4a94-b7c0-9f95b3e0be5c
-- title:
--   Light Ternary Enumeration: output length
-- statement:
--   The Light Ternary Enumeration construction uses the output length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L16-L17
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L16-L17

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEnumeration.output_length (N T pref : ℕ) :
    (output N T pref).length = (codes N T).length := by sorry
