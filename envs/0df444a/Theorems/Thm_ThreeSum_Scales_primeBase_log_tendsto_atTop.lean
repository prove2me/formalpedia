-- Prove2me | Theorems.Thm_ThreeSum_Scales_primeBase_log_tendsto_atTop
-- name    : ThreeSum.Scales.primeBase_log_tendsto_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:13:09.414935+00:00
-- url     : https://prove2.me/theorems/787b2f93-74ee-4c95-a332-2ce98a9eecb5
-- title:
--   Scales: prime Base log tendsto at Top
-- statement:
--   The Scales construction uses the prime Base log tendsto at Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L591-L594
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L591-L594

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

theorem ThreeSum.Scales.primeBase_log_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (4 * primeWindow n : ℝ)) atTop atTop := by sorry
