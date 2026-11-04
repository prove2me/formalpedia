-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalTensorHeader_args_safe
-- name    : ThreeSum.LightWeightedGlobalTensorHeader.args_safe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:45:06.642791+00:00
-- url     : https://prove2.me/theorems/d65c48e1-43f2-4d45-9c25-86857224dd25
-- title:
--   Light Weighted Global Tensor Header: args safe
-- statement:
--   The Light Weighted Global Tensor Header construction uses the args safe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorHeader.lean#L13-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorHeader.lean#L13-L26

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriverSyntax
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorHeader
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalTensorHeader
open Light LightWeightedGlobalTensorDriver

theorem ThreeSum.LightWeightedGlobalTensorHeader.args_safe {lim : Limits} (σ : State) (config : ℕ)
    (hconfig : σ.loc 0=(config : ℤ))
    (hspace : config+106≤lim.space) (hw : (lim.space : ℤ)≤lim.word) :
    ∀ e∈countArgs, e.Safe lim σ := by sorry
