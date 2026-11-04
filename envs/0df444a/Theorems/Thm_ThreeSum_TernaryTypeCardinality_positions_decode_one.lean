-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_decode_one
-- name    : ThreeSum.TernaryTypeCardinality.positions_decode_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:36.305321+00:00
-- url     : https://prove2.me/theorems/fb1f4a35-dea0-474b-968a-a77bafff84d8
-- title:
--   Ternary Type Cardinality: positions decode one
-- statement:
--   The Ternary Type Cardinality construction uses the positions decode one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L94-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L94-L101

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.positions_decode_one {L : ℕ} (p : Pair L) (hd : Disjoint p.1 p.2) :
    positions (decode p) 1=p.2 := by sorry
