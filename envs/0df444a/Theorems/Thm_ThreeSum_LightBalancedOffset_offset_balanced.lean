-- Prove2me | Theorems.Thm_ThreeSum_LightBalancedOffset_offset_balanced
-- name    : ThreeSum.LightBalancedOffset.offset_balanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:13:14.803851+00:00
-- url     : https://prove2.me/theorems/84e04f1e-93e5-4c49-82b9-ee5975474255
-- title:
--   Light Balanced Offset: offset balanced
-- statement:
--   The Light Balanced Offset construction uses the offset balanced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedOffset.lean#L23-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedOffset.lean#L23-L34

import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedOffset
open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators

theorem ThreeSum.LightBalancedOffset.offset_balanced {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) :
    p * Balancing.correlation F H (offset F H : ZMod p) ≤
      (∑ z, F z) * (∑ z, H z) := by sorry
