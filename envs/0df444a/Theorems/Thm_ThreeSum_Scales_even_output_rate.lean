-- Prove2me | Theorems.Thm_ThreeSum_Scales_even_output_rate
-- name    : ThreeSum.Scales.even_output_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:35:26.487937+00:00
-- url     : https://prove2.me/theorems/09fd9e89-e08a-4b8f-8753-b511df29c094
-- title:
--   Scales: even output rate
-- statement:
--   The Scales construction uses the even output rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L443-L455
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L443-L455

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

theorem ThreeSum.Scales.even_output_rate :
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.outputCount (512 * h) h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (2 * Parameters.E)) := by sorry
