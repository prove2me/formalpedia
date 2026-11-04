-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_encode_mem
-- name    : ThreeSum.TernaryTypeCardinality.encode_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:05.877832+00:00
-- url     : https://prove2.me/theorems/1fcd0041-f690-42bb-99b1-f1b134b259b4
-- title:
--   Ternary Type Cardinality: encode mem
-- statement:
--   The Ternary Type Cardinality construction uses the encode mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L78-L87
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L78-L87

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.encode_mem {L : ℕ} (π : DigitType) {w : TritWord L} (hw : HasType w π) :
    encode w∈digitPairs L (π 1) (π 2) := by sorry
