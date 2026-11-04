-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_digitPairs_card
-- name    : ThreeSum.TernaryTypeCardinality.digitPairs_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:27.774028+00:00
-- url     : https://prove2.me/theorems/396c8283-439c-4308-ac45-a8ccae73ae55
-- title:
--   Ternary Type Cardinality: digit Pairs card
-- statement:
--   The Ternary Type Cardinality construction uses the digit Pairs card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L139-L150
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L139-L150

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.digitPairs_card (L a b : ℕ) :
    (digitPairs L a b).card=L.choose b*(L-b).choose a := by sorry
