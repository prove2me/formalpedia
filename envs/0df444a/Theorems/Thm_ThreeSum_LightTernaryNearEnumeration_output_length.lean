-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_output_length
-- name    : ThreeSum.LightTernaryNearEnumeration.output_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:41:54.692123+00:00
-- url     : https://prove2.me/theorems/be2cc5c7-a5e4-421f-94c6-1479769faa63
-- title:
--   Light Ternary Near Enumeration: output length
-- statement:
--   The Light Ternary Near Enumeration construction uses the output length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean#L29-L30
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean#L29-L30

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_output_length
import Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_length
attribute [local simp] ThreeSum.LightSubsetEnumeration.output_length
attribute [local simp] ThreeSum.LightTernaryEnumeration.output_length


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryNearEnumeration.output_length (qs : List ℕ) (D pref : ℕ) :
    (output qs D pref).length = (words qs D).length := by sorry
