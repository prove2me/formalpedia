-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryEnumeration_output_succ_full
-- name    : ThreeSum.LightTernaryEnumeration.output_succ_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:32.272199+00:00
-- url     : https://prove2.me/theorems/1fe1550c-f67e-4bea-a268-883ab5a88ef3
-- title:
--   Light Ternary Enumeration: output succ full
-- statement:
--   The Light Ternary Enumeration construction uses the output succ full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L36-L40
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryEnumeration.lean#L36-L40

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEnumeration
open Light ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryEnumeration.output_succ_full {T : ℕ} (hT : 2 ≤ T) (N pref : ℕ) :
    output (N+1) T pref = output N T pref ++
      output N (T-1) (pref+4^N) ++ output N (T-2) (pref+3*4^N) := by sorry
