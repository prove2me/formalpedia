-- Prove2me | Theorems.Thm_ThreeSum_TernaryAddresses_codes_eq_map
-- name    : ThreeSum.TernaryAddresses.codes_eq_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:57.929173+00:00
-- url     : https://prove2.me/theorems/2e69760a-a6f8-4c78-82ce-5872bf23d324
-- title:
--   Ternary Addresses: codes eq map
-- statement:
--   The Ternary Addresses construction uses the codes eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryAddresses.lean#L45-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryAddresses.lean#L45-L57

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration

theorem ThreeSum.TernaryAddresses.codes_eq_map (n t : ℕ) : codes n t = (words n t).map code := by sorry
