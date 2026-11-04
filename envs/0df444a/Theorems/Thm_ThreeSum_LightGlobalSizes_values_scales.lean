-- Prove2me | Theorems.Thm_ThreeSum_LightGlobalSizes_values_scales
-- name    : ThreeSum.LightGlobalSizes.values_scales
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:19:38.134+00:00
-- url     : https://prove2.me/theorems/c484380b-fe8d-4029-a5e1-3d04ae32eae3
-- title:
--   Light Global Sizes: values scales
-- statement:
--   The Light Global Sizes construction uses the values scales property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean#L189-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightGlobalSizes.lean#L189-L194

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

theorem ThreeSum.LightGlobalSizes.values_scales (n : ℕ) :
    values (localCount n) (Scales.localRadix n) (Scales.blockCount (Scales.inputBits n)) (Scales.mu n) =
      [(Scales.typedOutputs n : ℤ),Scales.radix n,BandScales.bandRoot n,
        BandScales.bandDivisor n,BandScales.bandSize n] := by sorry
