-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEnumeration_digits_full
-- name    : ThreeSum.LightTernaryEnumeration.digits_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:57.958539+00:00
-- url     : https://prove2.me/theorems/b6025be3-6b72-4b5d-bbed-f3dc2a05dfb8
-- title:
--   Light Ternary Enumeration: digits full
-- statement:
--   The Light Ternary Enumeration construction uses the digits full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L24-L25
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L24-L25

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEnumeration.digits_full {T : ℕ} (hT : 2 ≤ T) : digits T = [0,1,2] := by sorry
