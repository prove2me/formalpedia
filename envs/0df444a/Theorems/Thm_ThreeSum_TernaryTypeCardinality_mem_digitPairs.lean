-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_mem_digitPairs
-- name    : ThreeSum.TernaryTypeCardinality.mem_digitPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:06:53.113755+00:00
-- url     : https://prove2.me/theorems/14380447-25e5-4312-8521-15eb58b13f2d
-- title:
--   Ternary Type Cardinality: mem digit Pairs
-- statement:
--   The Ternary Type Cardinality construction uses the mem digit Pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L64-L76
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L64-L76

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.mem_digitPairs {L a b : ℕ} (p : Pair L) :
    p∈digitPairs L a b ↔ p.1.card=b ∧ p.2.card=a ∧ Disjoint p.1 p.2 := by sorry
