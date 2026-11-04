-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_space_eq
-- name    : ThreeSum.EncodedColorPrimeCosts.space_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T13:26:14.886927+00:00
-- url     : https://prove2.me/theorems/6e56dfa6-709a-4e80-b421-e7c9c4b5642e
-- title:
--   Encoded Color Prime Costs: space eq
-- statement:
--   The Encoded Color Prime Costs construction uses the space eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeCosts.lean#L20-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeCosts.lean#L20-L22

import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrime
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeCosts
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeCosts
open Light Scales BandScales CostLedger ArithmeticStageBounds

theorem ThreeSum.EncodedColorPrimeCosts.space_eq (free maxMod g M y U : ℕ) :
    LightEncodedColorPrimeCore.space free maxMod g M y U=
      LightBandPrimeSetup.space (EncodedColorPrimeData.poolBase free) maxMod g M y U := by sorry
