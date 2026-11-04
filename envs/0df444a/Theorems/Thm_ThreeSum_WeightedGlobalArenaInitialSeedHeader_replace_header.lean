-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaInitialSeedHeader_replace_header
-- name    : ThreeSum.WeightedGlobalArenaInitialSeedHeader.replace_header
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T23:19:11.021195+00:00
-- url     : https://prove2.me/theorems/cf5468c9-8733-467e-8fe8-3d134405985e
-- title:
--   Weighted Global Arena Initial Seed Header: replace header
-- statement:
--   The Weighted Global Arena Initial Seed Header construction uses the replace header property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean#L55-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaInitialSeedHeader.lean#L55-L58

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixCommit
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Definitions.Def_Submission_Weighted_Global_LightTernaryArenaTemplate
import Definitions.Def_Submission_Weighted_Global_TernaryPrefixSeedHeader
import Definitions.Def_Submission_Weighted_Global_TernaryArenaInitialSeedHeader
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaInitialSeedHeader
open Light WeightedGlobalArenaLayout WeightedGlobalArenaSourceSetup WeightedGlobalArenaSeedCandidate
open LightWeightedGlobalSeedScoreFactory LightWeightedGlobalControllerFactory LightWeightedGlobalPrefixHeader LightWeightedGlobalPrefixFinish
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem ThreeSum.WeightedGlobalArenaInitialSeedHeader.replace_header (C : Config) (n dB dC dP tB tC tP dB' dC' dP' tB' tC' tP' newSpan : ℕ) :
    replace (header C n dB dC dP tB tC tP newSpan) dB' dC' dP' tB' tC' tP'=
      header C n dB' dC' dP' tB' tC' tP' newSpan := by sorry
