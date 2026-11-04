-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_positions_card
-- name    : ThreeSum.TernaryTypeCardinality.positions_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:17:34.288846+00:00
-- url     : https://prove2.me/theorems/01fa63cd-f1a7-43d1-a8d6-11ac17533211
-- title:
--   Ternary Type Cardinality: positions card
-- statement:
--   The Ternary Type Cardinality construction uses the positions card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L17-L19
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L17-L19

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.positions_card {L : ℕ} (w : TritWord L) (d : Fin 3) :
    (positions w d).card=digitCount w d := by sorry
