-- Prove2me | Theorems.Thm_ThreeSum_TernaryAddresses_digitCode_strict
-- name    : ThreeSum.TernaryAddresses.digitCode_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:48.742876+00:00
-- url     : https://prove2.me/theorems/6423a0db-9ea6-44d0-bd31-a09cdbfacff8
-- title:
--   Ternary Addresses: digit Code strict
-- statement:
--   The Ternary Addresses construction uses the digit Code strict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryAddresses.lean#L31-L33
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryAddresses.lean#L31-L33

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration

theorem ThreeSum.TernaryAddresses.digitCode_strict {d e : ℕ} (hd : d < 3) (he : e < 3) (hde : d < e) :
    digitCode d < digitCode e := by sorry
