-- Prove2me | Theorems.Thm_ThreeSum_Scales_muZero_eq_twice_half
-- name    : ThreeSum.Scales.muZero_eq_twice_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:24.412208+00:00
-- url     : https://prove2.me/theorems/50beca43-9669-4d99-bfce-f4ff6a38db9a
-- title:
--   Scales: mu Zero eq twice half
-- statement:
--   The Scales construction uses the mu Zero eq twice half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L441-L441
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L441-L441

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

theorem ThreeSum.Scales.muZero_eq_twice_half (n : ℕ) : muZero n = 2 * microHalf (inputBits n) := by sorry
