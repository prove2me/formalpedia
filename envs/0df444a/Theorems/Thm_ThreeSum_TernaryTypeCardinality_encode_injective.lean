-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_encode_injective
-- name    : ThreeSum.TernaryTypeCardinality.encode_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:50:49.117783+00:00
-- url     : https://prove2.me/theorems/72da6135-4a3c-47de-a21b-8e4b41ef752d
-- title:
--   Ternary Type Cardinality: encode injective
-- statement:
--   The Ternary Type Cardinality construction uses the encode injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L59-L62
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L59-L62

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.encode_injective (L : ℕ) : Function.Injective (@encode L) := by sorry
