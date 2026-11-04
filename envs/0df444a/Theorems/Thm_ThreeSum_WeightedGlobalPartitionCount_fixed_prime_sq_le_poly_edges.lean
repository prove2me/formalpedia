-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_fixed_prime_sq_le_poly_edges
-- name    : ThreeSum.WeightedGlobalPartitionCount.fixed_prime_sq_le_poly_edges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:26.897518+00:00
-- url     : https://prove2.me/theorems/6a48b65e-b74b-4bd1-a0cd-542c5d0d3a36
-- title:
--   Weighted Global Partition Count: fixed prime sq le poly edges
-- statement:
--   The Weighted Global Partition Count construction uses the fixed prime sq le poly edges property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L287-L292
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryPartitionCount.lean#L287-L292

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_ThreeSum_TernaryTypeLowerBound
import Definitions.Def_Submission_ThreeSum_LocalGraph
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Definitions.Def_Submission_Weighted_GlobalLocalParameters
import Mathlib.Tactic
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound
open WeightedGlobalLocalParameters

theorem ThreeSum.WeightedGlobalPartitionCount.fixed_prime_sq_le_poly_edges (m p : ℕ)
    (hP : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2))) :
    p^2 ≤ 16*partitionLoss (2380004124000*m) (292746547000*m)*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)) := by sorry
