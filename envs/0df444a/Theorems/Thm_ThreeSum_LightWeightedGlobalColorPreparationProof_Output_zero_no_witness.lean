-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedGlobalColorPreparationProof_Output_zero_no_witness
-- name    : ThreeSum.LightWeightedGlobalColorPreparationProof.Output.zero_no_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:18:47.187375+00:00
-- url     : https://prove2.me/theorems/e5931643-3f84-4daa-a4ad-9a7939063dd0
-- title:
--   Output: zero no witness
-- statement:
--   Skipping a zero-returned color is sound on the original input.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparationProof.lean#L567-L578
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/LightTernaryColorPreparationProof.lean#L567-L578

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryColorPreparationLayout
import Definitions.Def_Submission_Weighted_Global_LightTernaryColorPreparationProof
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalColorPreparationProof
open Light LightWeightedGlobalColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

theorem ThreeSum.LightWeightedGlobalColorPreparationProof.Output.zero_no_witness {n free U R J q menu radix : ℕ}
    {μ ν : ℕ→ℤ} {p : Coloring.Parameter (width n)} {x : Fin n→ℤ}
    (H : Output μ ν free U R J q menu radix p x 0) :
    ¬ColorClassLists.witness p x := by sorry
