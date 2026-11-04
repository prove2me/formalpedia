-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_succ_zero
-- name    : ThreeSum.LightTernaryEnumeration.output_succ_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:40.060522+00:00
-- url     : https://prove2.me/theorems/83fba2d6-71dd-4565-972a-74d57543d647
-- title:
--   Light Ternary Enumeration: output succ zero
-- statement:
--   The Light Ternary Enumeration construction uses the output succ zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L27-L29
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L27-L29

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEnumeration.output_succ_zero (N pref : ℕ) :
    output (N+1) 0 pref = output N 0 pref := by sorry
