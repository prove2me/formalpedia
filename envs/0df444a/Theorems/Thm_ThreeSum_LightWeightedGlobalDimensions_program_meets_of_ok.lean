-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalDimensions_program_meets_of_ok
-- name    : ThreeSum.LightWeightedGlobalDimensions.program_meets_of_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:51:25.290815+00:00
-- url     : https://prove2.me/theorems/04893a49-640f-4c53-b8db-071cfe336d01
-- title:
--   Light Weighted Global Dimensions: program meets of ok
-- statement:
--   The Light Weighted Global Dimensions construction uses the program meets of ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L108-L116
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryDimensionsBudget.lean#L108-L116

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensions
import Definitions.Def_Submission_Weighted_Global_TernaryExtensionBudget
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_Weighted_Global_LightTernaryDimensionsBudget
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalDimensions
open Light WeightedGlobalSignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

theorem ThreeSum.LightWeightedGlobalDimensions.program_meets_of_ok {lim : Limits} {M b p K n U dst depth : ℕ} [Fact p.Prime]
    (μ : ℕ → ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (hok : (need M b p K n U).Ok lim dst depth) :
    Meets lim (program M b p K) 0 depth [n,U,dst] μ (time M b p K n U)
      (fun z ν => z=((p^(dim M b p K n U) : ℕ) : ℤ) ∧
        Seg ν dst [(r M n : ℤ),J M b n U,dim M b p K n U,(p^(dim M b p K n U) : ℕ)] ∧
        Kept μ ν dst) := by sorry
