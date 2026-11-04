-- Prove2me | Theorems.Thm_ThreeSum_Scales_log_bits_over_primeBase_tendsto_zero
-- name    : ThreeSum.Scales.log_bits_over_primeBase_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:35:49.047019+00:00
-- url     : https://prove2.me/theorems/049de0b2-5ad5-43cf-95e1-ec2cca941cfe
-- title:
--   Scales: log bits over prime Base tendsto zero
-- statement:
--   The Scales construction uses the log bits over prime Base tendsto zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L765-L790
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Scales.lean#L765-L790

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

theorem ThreeSum.Scales.log_bits_over_primeBase_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (inputBits n + 1 : ℝ) /
      Real.log (4 * primeWindow n : ℝ)) atTop (𝓝 0) := by sorry
