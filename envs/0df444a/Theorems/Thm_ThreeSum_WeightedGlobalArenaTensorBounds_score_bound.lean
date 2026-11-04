-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalArenaTensorBounds_score_bound
-- name    : ThreeSum.WeightedGlobalArenaTensorBounds.score_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T21:15:00.350203+00:00
-- url     : https://prove2.me/theorems/701e5f75-ce71-473c-828c-32cf95a3f4be
-- title:
--   Weighted Global Arena Tensor Bounds: score bound
-- statement:
--   Exact native physical-pair bound; every map occurrence and tuple remains
--   in the count. The larger power is used solely for word resources.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean#L21-L46
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaTensorBounds.lean#L21-L46

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaFrontBounds
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Definitions.Def_Submission_Weighted_Global_TernaryArenaTensorBounds
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaTensorBounds
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaSourceSetup WeightedGlobalArenaSourceBounds
open WeightedGlobalArenaFrontBounds WeightedGlobalCoverGoodMaps WeightedGlobalLocalParameters
open WeightedGlobalNativeCompleteFrontend WeightedGlobalNativeMomentBounds
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

theorem ThreeSum.WeightedGlobalArenaTensorBounds.score_bound (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : WeightedGlobalGoodOutputCatalog.Output m) (I : Input) (n U H : ℕ)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hw : I.weightCap≤weight H (4^fixedLength m) U) :
    scoreBound (setup (r := r) maps τ cap Q I)≤
      ((4^fixedLength m)^r)^2*n^2*((sourceWidth maps cap)^r)^2*
        (weight H (4^fixedLength m) U)^2 := by sorry
