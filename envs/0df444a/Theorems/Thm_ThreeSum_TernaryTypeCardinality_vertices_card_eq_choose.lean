-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_vertices_card_eq_choose
-- name    : ThreeSum.TernaryTypeCardinality.vertices_card_eq_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:50.97865+00:00
-- url     : https://prove2.me/theorems/27c330a3-2af3-4132-a117-4aebe2f20f9d
-- title:
--   Ternary Type Cardinality: vertices card eq choose
-- statement:
--   Exact cardinality of the actual fixed-type vertex table used by the cover.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L153-L155
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L153-L155

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.vertices_card_eq_choose {L : ℕ} (π : DigitType) (htotal : π 0+π 1+π 2=L) :
    (vertices L π).card=L.choose (π 2)*(L-π 2).choose (π 1) := by sorry
