-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAResources_space_eq
-- name    : ThreeSum.LightBandRawAResources.space_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:58:44.28437+00:00
-- url     : https://prove2.me/theorems/acf770fd-b48d-4311-a259-ae7711a9ede1
-- title:
--   Light Band Raw AResources: space eq
-- statement:
--   The Light Band Raw AResources construction uses the space eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean#L21-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean#L21-L26

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

theorem ThreeSum.LightBandRawAResources.space_eq (free W n g : ℕ) :
    LightBandRawAColor.space (tables free n) (vals free n g) W n g = free + cells W n g := by sorry
