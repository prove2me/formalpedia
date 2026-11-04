-- Prove2me | Theorems.Thm_ThreeSum_Scales_input_log_le_bits_add_one
-- name    : ThreeSum.Scales.input_log_le_bits_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:35:43.417473+00:00
-- url     : https://prove2.me/theorems/b21c9b6b-162c-4dfd-86da-54064771b810
-- title:
--   Scales: input log le bits add one
-- statement:
--   The Scales construction uses the input log le bits add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L644-L655
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L644-L655

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

theorem ThreeSum.Scales.input_log_le_bits_add_one {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) ≤ inputBits n + 1 := by sorry
