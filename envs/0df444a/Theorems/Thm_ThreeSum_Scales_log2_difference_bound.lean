-- Prove2me | Theorems.Thm_ThreeSum_Scales_log2_difference_bound
-- name    : ThreeSum.Scales.log2_difference_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:13:00.664452+00:00
-- url     : https://prove2.me/theorems/f8703e7f-b20e-4799-a8c1-c1df27edd464
-- title:
--   Scales: log2 difference bound
-- statement:
--   The Scales construction uses the log2 difference bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L886-L897
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L886-L897

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

theorem ThreeSum.Scales.log2_difference_bound (k : ℕ) {n : ℕ} (hn : 0 < n) :
    Nat.log2 (3 * n ^ k) ≤ 2 * (k + 2) * (inputBits n + 1) := by sorry
