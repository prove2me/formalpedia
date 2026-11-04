-- Prove2me | Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
-- name    : ThreeSum.TernaryAddresses.codes_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:24:52.551483+00:00
-- url     : https://prove2.me/theorems/73bd0a3b-c7b3-408b-99ca-e947c48d6b53
-- title:
--   Ternary Addresses: codes length
-- statement:
--   The Ternary Addresses construction uses the codes length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryAddresses.lean#L59-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryAddresses.lean#L59-L60

import Definitions.Def_Submission_ThreeSum_TernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddresses
open ThreeSum.TernaryEnumeration

theorem ThreeSum.TernaryAddresses.codes_length (n t : ℕ) : (codes n t).length = (words n t).length := by sorry
