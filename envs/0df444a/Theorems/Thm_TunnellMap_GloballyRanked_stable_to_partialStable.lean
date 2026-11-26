-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_stable_to_partialStable
-- name    : TunnellMap.GloballyRanked.stable_to_partialStable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:08.36104+00:00
-- url     : https://prove2.me/theorems/0e2da11f-6a73-5b24-b219-daa680a6e5f0
-- title:
--   Globally Ranked: stable to partial Stable
-- statement:
--   A stable perfect matching is stable when regarded as a partial matching.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PartialStableMatching.lean#L42-L46
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PartialStableMatching.lean#L42-L46

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_PartialStableMatching
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}

theorem TunnellMap.GloballyRanked.stable_to_partialStable [LT K] (I : GloballyRanked K S T) (M : S ≃ T)
    (hM : I.Stable M) : I.PartialStable M.toPartialEquiv := by sorry
