-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_decode_encode
-- name    : ThreeSum.TernaryTypeCardinality.decode_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:52.910922+00:00
-- url     : https://prove2.me/theorems/b7788e6c-b814-4f6b-9f8f-3bf70f438f40
-- title:
--   Ternary Type Cardinality: decode encode
-- statement:
--   The Ternary Type Cardinality construction uses the decode encode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L52-L57
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L52-L57

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.decode_encode {L : ℕ} (w : TritWord L) : decode (encode w)=w := by sorry
