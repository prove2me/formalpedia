-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_time_eq
-- name    : ThreeSum.EncodedColorPrimeCosts.time_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:34:41.492266+00:00
-- url     : https://prove2.me/theorems/5a073344-8189-4f8c-bdbc-a7a09573f723
-- title:
--   Encoded Color Prime Costs: time eq
-- statement:
--   The Encoded Color Prime Costs construction uses the time eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeCosts.lean#L15-L18
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeCosts.lean#L15-L18

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds

theorem ThreeSum.EncodedColorPrimeCosts.time_eq (maxMod nA nB nC g M y U : ℕ) :
    LightEncodedColorPrime.time maxMod nA nB nC g M y U=
      LightBandPrimeSetup.time maxMod g (LightEncodedColorPrime.count nA nB nC g) M y U+1160 := by sorry
