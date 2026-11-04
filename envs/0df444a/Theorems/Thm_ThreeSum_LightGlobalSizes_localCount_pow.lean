-- Prove2me | Theorems.Thm_ThreeSum_LightGlobalSizes_localCount_pow
-- name    : ThreeSum.LightGlobalSizes.localCount_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:38.073541+00:00
-- url     : https://prove2.me/theorems/ac7bf04a-6e32-401a-afad-d4eeba2906a4
-- title:
--   Light Global Sizes: local Count pow
-- statement:
--   The Light Global Sizes construction uses the local Count pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean#L180-L187
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean#L180-L187

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_BandScales
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Sqrt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSum_LightGlobalSizes
set_option autoImplicit false
open ThreeSum ThreeSum.LightGlobalSizes
set_option maxHeartbeats 1000000
open Light LocalCoverBounds
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightGlobalSizes.localCount_pow (n : ℕ) :
    localCount n ^ Scales.blockCount (Scales.inputBits n) = Scales.typedOutputs n := by sorry
