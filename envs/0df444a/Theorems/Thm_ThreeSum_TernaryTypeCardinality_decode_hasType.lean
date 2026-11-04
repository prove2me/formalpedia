-- Prove2me | Theorems.Thm_ThreeSum_TernaryTypeCardinality_decode_hasType
-- name    : ThreeSum.TernaryTypeCardinality.decode_hasType
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:51:04.90729+00:00
-- url     : https://prove2.me/theorems/b15d88c7-5a11-4b49-a3f7-6e2dcd1d60b8
-- title:
--   Ternary Type Cardinality: decode has Type
-- statement:
--   The Ternary Type Cardinality construction uses the decode has Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L111-L124
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryTypeCardinality.lean#L111-L124

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryTypeCardinality
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryCoverLocal
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryTypeCardinality.decode_hasType {L : ℕ} (π : DigitType) (htotal : π 0+π 1+π 2=L)
    (p : Pair L) (hp : p∈digitPairs L (π 1) (π 2)) : HasType (decode p) π := by sorry
