-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_disjoint
-- name    : ThreeSum.TernaryTypeCardinality.positions_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:47.394205+00:00
-- url     : https://prove2.me/theorems/35473af6-861c-4441-b2f2-8ca5d9f623a4
-- title:
--   Ternary Type Cardinality: positions disjoint
-- statement:
--   The Ternary Type Cardinality construction uses the positions disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L21-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L21-L28

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.positions_disjoint {L : ℕ} (w : TritWord L) :
    Disjoint (positions w 2) (positions w 1) := by sorry
