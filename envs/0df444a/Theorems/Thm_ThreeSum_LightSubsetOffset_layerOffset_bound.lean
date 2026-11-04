-- Prove2me | Theorems.Thm_ThreeSum_LightSubsetOffset_layerOffset_bound
-- name    : ThreeSum.LightSubsetOffset.layerOffset_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:32:26.435397+00:00
-- url     : https://prove2.me/theorems/13a6b753-bb9e-429b-ab10-3e4edacc5680
-- title:
--   Light Subset Offset: layer Offset bound
-- statement:
--   The Light Subset Offset construction uses the layer Offset bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetOffset.lean#L11-L17
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSubsetOffset.lean#L11-L17

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetOffset
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSubsetOffset.layerOffset_bound (L k : ℕ) : layerOffset L k ≤ k*2^L := by sorry
