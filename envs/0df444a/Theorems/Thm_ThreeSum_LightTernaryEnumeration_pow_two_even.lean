-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEnumeration_pow_two_even
-- name    : ThreeSum.LightTernaryEnumeration.pow_two_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:33:11.504635+00:00
-- url     : https://prove2.me/theorems/a375383d-0342-48e8-9894-88035a5c3dbe
-- title:
--   Light Ternary Enumeration: pow two even
-- statement:
--   The Light Ternary Enumeration construction uses the pow two even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L71-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L71-L73

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEnumeration.pow_two_even (N : ℕ) : 2^(2*N) = 4^N := by sorry
