-- Prove2me | Theorems.Thm_ThreeSum_ThreeSumParameterResources_global_word_le
-- name    : ThreeSum.ThreeSumParameterResources.global_word_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T15:02:56.408045+00:00
-- url     : https://prove2.me/theorems/5163ffa9-2650-4469-b9ec-cefdd2dd9d11
-- title:
--   Three Sum Parameter Resources: global word le
-- statement:
--   The Three Sum Parameter Resources construction uses the global word le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumParameterResources.lean#L49-L64
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ThreeSumParameterResources.lean#L49-L64

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000

theorem ThreeSum.ThreeSumParameterResources.global_word_le (n : ℕ) :
    LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n)
      (blockCount (inputBits n)) (mu n) ≤ 8000*scale n := by sorry
