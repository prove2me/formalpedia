-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_partialStable_unique
-- name    : TunnellMap.GloballyRanked.partialStable_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:31.162713+00:00
-- url     : https://prove2.me/theorems/3195b0f3-71e5-5411-a588-c7290b9ad2ee
-- title:
--   Globally Ranked: partial Stable unique
-- statement:
--   Any two stable partial matchings on finite equal sides coincide.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PartialStableMatching.lean#L99-L116
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PartialStableMatching.lean#L99-L116

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_PartialStableMatching
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}

theorem TunnellMap.GloballyRanked.partialStable_unique [LinearOrder K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T)
    (M N : PartialEquiv S T) (hM : I.PartialStable M)
    (hN : I.PartialStable N) : M = N := by sorry
