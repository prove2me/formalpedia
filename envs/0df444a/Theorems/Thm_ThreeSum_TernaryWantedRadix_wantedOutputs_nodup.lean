-- Prove2me | Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedOutputs_nodup
-- name    : ThreeSum.TernaryWantedRadix.wantedOutputs_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:09:54.148461+00:00
-- url     : https://prove2.me/theorems/171b2184-5651-424f-8b7f-f1b6a80aed4a
-- title:
--   Ternary Wanted Radix: wanted Outputs nodup
-- statement:
--   The Ternary Wanted Radix construction uses the wanted Outputs nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L48-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWantedRadix.lean#L48-L61

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset

theorem ThreeSum.TernaryWantedRadix.wantedOutputs_nodup (p : ℤ) (raws : List ℤ) : ∀ j x, (wantedOutputs p raws j x).Nodup := by sorry
