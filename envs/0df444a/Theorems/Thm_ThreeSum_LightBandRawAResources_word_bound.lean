-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAResources_word_bound
-- name    : ThreeSum.LightBandRawAResources.word_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:34:21.439266+00:00
-- url     : https://prove2.me/theorems/3132dcda-bedd-407b-9e80-efe0224b07d2
-- title:
--   Light Band Raw AResources: word bound
-- statement:
--   The Light Band Raw AResources construction uses the word bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResourcesScales.lean#L44-L54
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResourcesScales.lean#L44-L54

import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsPolynomial
import Definitions.Def_Submission_ThreeSum_LightColorParametersCosts
import Definitions.Def_Submission_ThreeSum_LightBandRawAResourcesScales
import Theorems.Thm_ThreeSum_LocalParameterBounds_word_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light Scales BandScales StageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

theorem ThreeSum.LightBandRawAResources.word_bound (n U : ℕ) :
    LightBandRawAColor.word (inputBits n+1) n (bandSize n) U ≤ envelope n*(U+1) := by sorry
