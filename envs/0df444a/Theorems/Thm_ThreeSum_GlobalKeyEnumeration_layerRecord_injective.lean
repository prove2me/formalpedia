-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyEnumeration_layerRecord_injective
-- name    : ThreeSum.GlobalKeyEnumeration.layerRecord_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:11:14.048726+00:00
-- url     : https://prove2.me/theorems/900e90a6-f04c-40a4-be08-305573826539
-- title:
--   Global Key Enumeration: layer Record injective
-- statement:
--   The Global Key Enumeration construction uses the layer Record injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L28-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L28-L31

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem ThreeSum.GlobalKeyEnumeration.layerRecord_injective (h : ℕ) : Function.Injective (layerRecord h) := by sorry
