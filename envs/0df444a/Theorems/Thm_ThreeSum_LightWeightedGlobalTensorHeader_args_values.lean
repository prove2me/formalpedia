-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalTensorHeader_args_values
-- name    : ThreeSum.LightWeightedGlobalTensorHeader.args_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:45:41.491513+00:00
-- url     : https://prove2.me/theorems/1684604d-5a81-4a95-a357-ec5c8eb3f086
-- title:
--   Light Weighted Global Tensor Header: args values
-- statement:
--   The Light Weighted Global Tensor Header construction uses the args values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorHeader.lean#L28-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryTensorHeader.lean#L28-L36

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorDriverSyntax
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorHeader
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalTensorHeader
open Light LightWeightedGlobalTensorDriver

theorem ThreeSum.LightWeightedGlobalTensorHeader.args_values (σ : State) (config : ℕ) (vals : List ℤ)
    (hconfig : σ.loc 0=(config : ℤ)) (hlen : vals.length=106)
    (hread : ∀ i<106, σ.mem (config+i)=vals.getD i 0) :
    countArgs.map (·.val σ)=vals := by sorry
