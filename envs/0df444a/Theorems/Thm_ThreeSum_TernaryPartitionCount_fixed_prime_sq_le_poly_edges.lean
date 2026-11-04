-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartitionCount_fixed_prime_sq_le_poly_edges
-- name    : ThreeSum.TernaryPartitionCount.fixed_prime_sq_le_poly_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:49:33.146899+00:00
-- url     : https://prove2.me/theorems/d4f3d324-84f8-4b2b-93a8-179fd6a454ba
-- title:
--   Ternary Partition Count: fixed prime sq le poly edges
-- statement:
--   The Ternary Partition Count construction uses the fixed prime sq le poly edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L280-L285
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L280-L285

import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_ThreeSum_TernaryLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound
open TernaryLocalParameters

theorem ThreeSum.TernaryPartitionCount.fixed_prime_sq_le_poly_edges (m p : ℕ)
    (hP : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2))) :
    p^2 ≤ 16*partitionLoss (7930225*m) (978268*m)*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)) := by sorry
