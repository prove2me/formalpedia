-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_vertices_card_eq_pairs
-- name    : ThreeSum.TernaryTypeCardinality.vertices_card_eq_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:05.970197+00:00
-- url     : https://prove2.me/theorems/d245bf81-45f3-4c7f-8f93-a4c3b3992d70
-- title:
--   Ternary Type Cardinality: vertices card eq pairs
-- statement:
--   The Ternary Type Cardinality construction uses the vertices card eq pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L126-L137
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L126-L137

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.vertices_card_eq_pairs {L : ℕ} (π : DigitType) (htotal : π 0+π 1+π 2=L) :
    (vertices L π).card=(digitPairs L (π 1) (π 2)).card := by sorry
