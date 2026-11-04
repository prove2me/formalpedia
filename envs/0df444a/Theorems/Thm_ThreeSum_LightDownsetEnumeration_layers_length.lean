-- Prove2me | Theorems.Thm_ThreeSum_LightDownsetEnumeration_layers_length
-- name    : ThreeSum.LightDownsetEnumeration.layers_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:31:02.813567+00:00
-- url     : https://prove2.me/theorems/8e7c8c2d-38d3-4945-bc28-509986c21b12
-- title:
--   Light Downset Enumeration: layers length
-- statement:
--   The Light Downset Enumeration construction uses the layers length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumeration.lean#L22-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightDownsetEnumeration.lean#L22-L26

import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightDownsetEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetEnumeration
open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightDownsetEnumeration.layers_length (L j : ℕ) : (layers L j).length = layerOffset L j := by sorry
