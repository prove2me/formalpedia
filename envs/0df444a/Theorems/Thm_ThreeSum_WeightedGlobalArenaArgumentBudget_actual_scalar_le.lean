-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaArgumentBudget_actual_scalar_le
-- name    : ThreeSum.WeightedGlobalArenaArgumentBudget.actual_scalar_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T16:53:24.382706+00:00
-- url     : https://prove2.me/theorems/874b6149-0422-48db-a445-af67a928d1b2
-- title:
--   Weighted Global Arena Argument Budget: actual scalar le
-- statement:
--   The Weighted Global Arena Argument Budget construction uses the actual scalar le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaArgumentBudget.lean#L94-L107
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaArgumentBudget.lean#L94-L107

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaArgumentWords
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceControlBudget
import Definitions.Def_Submission_Weighted_Global_TernaryArenaArgumentBudget
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaArgumentBudget
open Light WeightedGlobalArenaSourceSetup WeightedGlobalArenaArgumentWords WeightedGlobalArenaSourceControlBudget
open WeightedGlobalLocalParameters

theorem ThreeSum.WeightedGlobalArenaArgumentBudget.actual_scalar_le {m p F M r n U count : ℕ}
    (hp : 1≤p) (hF : 1≤F) (hr : r≤Nat.clog M (n^2)) :
    scalarControl m p F r count≤(need m p F M n U).word+count := by sorry
