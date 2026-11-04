-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_encode_decode
-- name    : ThreeSum.TernaryTypeCardinality.encode_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:05.511062+00:00
-- url     : https://prove2.me/theorems/2cf85e3e-3710-496a-b181-a40c4433e688
-- title:
--   Ternary Type Cardinality: encode decode
-- statement:
--   The Ternary Type Cardinality construction uses the encode decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L103-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L103-L109

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.encode_decode {L : ℕ} (p : Pair L) (hd : Disjoint p.1 p.2) :
    encode (decode p)=p := by sorry
