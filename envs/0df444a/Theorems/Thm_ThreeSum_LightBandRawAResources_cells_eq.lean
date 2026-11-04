-- Prove2me | Theorems.Thm_ThreeSum_LightBandRawAResources_cells_eq
-- name    : ThreeSum.LightBandRawAResources.cells_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:35:06.497168+00:00
-- url     : https://prove2.me/theorems/e42fdadd-489c-42f6-8900-bc95d7bbdc05
-- title:
--   Light Band Raw AResources: cells eq
-- statement:
--   The Light Band Raw AResources construction uses the cells eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean#L28-L34
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandRawAResources.lean#L28-L34

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

theorem ThreeSum.LightBandRawAResources.cells_eq (W n g : ℕ) :
    cells W n g =
      max (19 + 14 * n + ColorBandBounds.count n g + ColorBandBounds.width n g + W)
        (17 + 13 * n + 5 * ColorBandBounds.count n g + 3 * g * ColorBandBounds.count n g) := by sorry
