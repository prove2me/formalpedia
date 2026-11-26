-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_partialStable_to_stable
-- name    : TunnellMap.GloballyRanked.partialStable_to_stable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:45:44.730813+00:00
-- url     : https://prove2.me/theorems/8958473c-3cbf-4056-855b-59dfece38b1e
-- title:
--   Globally Ranked: partial Stable to stable
-- statement:
--   Once a stable partial matching is known to be perfect, it gives a stable
--   ordinary equivalence.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PartialStableMatching.lean#L86-L96
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PartialStableMatching.lean#L86-L96

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_PartialStableMatching
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}

theorem TunnellMap.GloballyRanked.partialStable_to_stable [LT K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T)
    (M : PartialEquiv S T) (hM : I.PartialStable M) :
    I.Stable (partialEquivToEquiv M
      (partialStable_isPerfect I hcard M hM).1
      (partialStable_isPerfect I hcard M hM).2) := by sorry
