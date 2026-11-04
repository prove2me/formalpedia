-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaArgumentBudget_scalar_le
-- name    : ThreeSum.WeightedGlobalArenaArgumentBudget.scalar_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:57:56.247271+00:00
-- url     : https://prove2.me/theorems/745c181c-34ea-46b5-9ae6-5f42c72541ae
-- title:
--   Weighted Global Arena Argument Budget: scalar le
-- statement:
--   The Weighted Global Arena Argument Budget construction uses the scalar le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaArgumentBudget.lean#L29-L88
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaArgumentBudget.lean#L29-L88

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaArgumentWords
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaArgumentBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaArgumentBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaArgumentWords WeightedGlobalArenaSourceControlBudget
open WeightedGlobalLocalParameters

theorem ThreeSum.WeightedGlobalArenaArgumentBudget.scalar_le (m p F r count B D : ℕ)
    (hbase : baseWord m p F r≤B) (hdepth : 2*N m r+r+8≤D) :
    scalarControl m p F r count≤16*(B+D+1)^2+count := by sorry
