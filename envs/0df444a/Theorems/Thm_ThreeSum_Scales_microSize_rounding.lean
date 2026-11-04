-- Prove2me | Theorems.Thm_ThreeSum_Scales_microSize_rounding
-- name    : ThreeSum.Scales.microSize_rounding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:20.045229+00:00
-- url     : https://prove2.me/theorems/dd39d9ab-b1a5-4837-ba7f-3a7f2850d664
-- title:
--   Scales: micro Size rounding
-- statement:
--   The Scales construction uses the micro Size rounding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L75-L80
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L75-L80

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_Asymptotics
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt
import Definitions.Def_Submission_ThreeSum_Scales
set_option autoImplicit false
open ThreeSum ThreeSum.Scales
open Filter Real
open scoped Topology

theorem ThreeSum.Scales.microSize_rounding (m : ℕ) :
    microSize m ≤ Nat.nthRoot 3 m ∧ Nat.nthRoot 3 m < microSize m + 2 := by sorry
