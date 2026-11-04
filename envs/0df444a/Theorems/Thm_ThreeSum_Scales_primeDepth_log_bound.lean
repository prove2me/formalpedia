-- Prove2me | Theorems.Thm_ThreeSum_Scales_primeDepth_log_bound
-- name    : ThreeSum.Scales.primeDepth_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:57.611682+00:00
-- url     : https://prove2.me/theorems/38de12b2-8c0c-4d5e-ba68-c4997863373b
-- title:
--   Scales: prime Depth log bound
-- statement:
--   The Scales construction uses the prime Depth log bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L578-L589
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L578-L589

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

theorem ThreeSum.Scales.primeDepth_log_bound {n : ℕ} (hR : 4 ≤ radix n) :
    (primeDepth radix n : ℝ) * Real.log (4 * primeWindow n : ℝ) ≤
      Real.log (radix n : ℝ) := by sorry
