-- Prove2me | Theorems.Thm_ThreeSum_LightBalancedOffset_offset_lt
-- name    : ThreeSum.LightBalancedOffset.offset_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:34:04.66339+00:00
-- url     : https://prove2.me/theorems/c784c35d-fe3d-4afd-a5e6-4939fbc791e0
-- title:
--   Light Balanced Offset: offset lt
-- statement:
--   The Light Balanced Offset construction uses the offset lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedOffset.lean#L20-L21
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBalancedOffset.lean#L20-L21

import Definitions.Def_Submission_ThreeSum_LightCyclic
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
set_option autoImplicit false
open ThreeSum ThreeSum.LightBalancedOffset
open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators

theorem ThreeSum.LightBalancedOffset.offset_lt {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) : offset F H < p := by sorry
