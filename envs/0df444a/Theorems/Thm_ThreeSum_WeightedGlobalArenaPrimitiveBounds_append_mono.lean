-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaPrimitiveBounds_append_mono
-- name    : ThreeSum.WeightedGlobalArenaPrimitiveBounds.append_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:29:08.691988+00:00
-- url     : https://prove2.me/theorems/fe372fd5-ee47-4ade-92be-f40f6997b4d1
-- title:
--   Weighted Global Arena Primitive Bounds: append mono
-- statement:
--   The Weighted Global Arena Primitive Bounds construction uses the append mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrimitiveBounds.lean#L19-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaPrimitiveBounds.lean#L19-L22

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceBounds
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSeedPrimitiveGuards
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrimitiveBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPrimitiveBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters WeightedGlobalNativeCompleteFrontend
open WeightedGlobalArenaSeedCandidate LightWeightedGlobalSeedScoreFactory
set_option maxHeartbeats 6000000
variable {p m F r : ℕ} [Fact p.Prime]

theorem ThreeSum.WeightedGlobalArenaPrimitiveBounds.append_mono {len p b power power' : ℕ} (hb : b≤p) (hp : power≤power') :
    LightTernaryAppendKeys.word len p b power≤LightTernaryAppendKeys.word len p p power' := by sorry
