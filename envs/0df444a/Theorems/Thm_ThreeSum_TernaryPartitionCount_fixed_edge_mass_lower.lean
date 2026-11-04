-- Prove2me | Theorems.Thm_ThreeSum_TernaryPartitionCount_fixed_edge_mass_lower
-- name    : ThreeSum.TernaryPartitionCount.fixed_edge_mass_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:59:16.225424+00:00
-- url     : https://prove2.me/theorems/fefe83c2-25e2-446e-96b7-061bed6021ce
-- title:
--   Ternary Partition Count: fixed edge mass lower
-- statement:
--   The Ternary Partition Count construction uses the fixed edge mass lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L262-L278
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPartitionCount.lean#L262-L278

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

theorem ThreeSum.TernaryPartitionCount.fixed_edge_mass_lower (m : ℕ) :
    (vertices (fixedLength m) (fixedPi m)).card*(2^(fixedPi m 1)*3^(fixedPi m 2)) ≤
    partitionLoss (7930225*m) (978268*m)*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)) := by sorry
