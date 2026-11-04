-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_decode_two
-- name    : ThreeSum.TernaryTypeCardinality.positions_decode_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:33.8122+00:00
-- url     : https://prove2.me/theorems/98c7696e-bea9-4543-b382-e5e861ed7530
-- title:
--   Ternary Type Cardinality: positions decode two
-- statement:
--   The Ternary Type Cardinality construction uses the positions decode two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L89-L92
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L89-L92

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.positions_decode_two {L : ℕ} (p : Pair L) : positions (decode p) 2=p.1 := by sorry
