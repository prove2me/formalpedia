-- Prove2me | Theorems.Thm_ThreeSum_TernaryAddresses_codes_nodup
-- name    : ThreeSum.TernaryAddresses.codes_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:58.402917+00:00
-- url     : https://prove2.me/theorems/8c51b748-75e2-4233-9fdc-171a39e4f6d7
-- title:
--   Ternary Addresses: codes nodup
-- statement:
--   The Ternary Addresses construction uses the codes nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryAddresses.lean#L90-L91
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryAddresses.lean#L90-L91

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration

theorem ThreeSum.TernaryAddresses.codes_nodup (n t : ℕ) : (codes n t).Nodup := by sorry
