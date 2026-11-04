-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalFastProgramProof_lift_global
-- name    : ThreeSum.LightWeightedGlobalFastProgramProof.lift_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T17:52:29.109532+00:00
-- url     : https://prove2.me/theorems/7dfbc607-95da-46b2-81b4-4daed5c8d4f9
-- title:
--   Light Weighted Global Fast Program Proof: lift global
-- statement:
--   The Light Weighted Global Fast Program Proof construction uses the lift global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryFastProgramProof.lean#L33-L43
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryFastProgramProof.lean#L33-L43

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgram
import Definitions.Def_Submission_Weighted_Global_TernaryGlobalPreludeTime
import Definitions.Def_Submission_Weighted_Global_LightTernaryFastProgramProof
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalFastProgramProof
open Light LightWeightedGlobalFastProgram LightWeightedGlobalGlobalPrelude
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalFastProgramProof.lift_global {lim : Limits} {M b p K κ entry depth T : ℕ}
    {vals : List ℤ} {μ : ℕ→ℤ} {Post : ℤ→(ℕ→ℤ)→Prop}
    (color : Program) (colorMain : ℕ)
    (h : Meets lim (LightWeightedGlobalGlobalPrelude.program M b p K κ) entry depth vals μ T Post) :
    Meets lim (program M b p K κ color colorMain) entry depth vals μ T Post := by sorry
