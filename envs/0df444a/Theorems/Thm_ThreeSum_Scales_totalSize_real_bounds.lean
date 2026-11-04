-- Prove2me | Theorems.Thm_ThreeSum_Scales_totalSize_real_bounds
-- name    : ThreeSum.Scales.totalSize_real_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:52.974943+00:00
-- url     : https://prove2.me/theorems/20231b1e-02c9-4faa-a708-c94a64f98574
-- title:
--   Scales: total Size real bounds
-- statement:
--   The Scales construction uses the total Size real bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L151-L158
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L151-L158

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
noncomputable section

theorem ThreeSum.Scales.totalSize_real_bounds {m : ℕ} (hm : 0 < microSize m) :
    (m : ℝ) / 5 - 20 * microSize m < totalSize m ∧
      (totalSize m : ℝ) ≤ (m : ℝ) / 5 := by sorry
