-- Prove2me | Theorems.Thm_ThreeSum_Scales_inputBits_eq_floor
-- name    : ThreeSum.Scales.inputBits_eq_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:51.176164+00:00
-- url     : https://prove2.me/theorems/5c37dedf-8086-40aa-8350-2da89f2bcd90
-- title:
--   Scales: input Bits eq floor
-- statement:
--   The Scales construction uses the input Bits eq floor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L181-L183
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L181-L183

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

theorem ThreeSum.Scales.inputBits_eq_floor (n : ℕ) : inputBits n = ⌊Real.logb 2 (n : ℝ)⌋₊ := by sorry
