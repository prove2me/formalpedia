-- Prove2me | Theorems.Thm_ThreeSum_GlobalKeyEnumeration_layers_length
-- name    : ThreeSum.GlobalKeyEnumeration.layers_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:08:57.215122+00:00
-- url     : https://prove2.me/theorems/eb97c22b-89da-446c-ab18-97fc86086ce3
-- title:
--   Global Key Enumeration: layers length
-- statement:
--   The Global Key Enumeration construction uses the layers length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L41-L42
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean#L41-L42

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

theorem ThreeSum.GlobalKeyEnumeration.layers_length (h : ℕ) : (layers h).length=outputCount (512*h) h := by sorry
