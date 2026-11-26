-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_existsUnique_partialStable
-- name    : TunnellMap.GloballyRanked.existsUnique_partialStable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:19:41.413941+00:00
-- url     : https://prove2.me/theorems/d182b56e-45eb-5427-af70-e2d6c0c6d1f2
-- title:
--   Globally Ranked: exists Unique partial Stable
-- statement:
--   Finite globally ranked complete bipartite instances with equal sides have
--   a unique stable matching even when partial matchings are admitted.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PartialStableMatching.lean#L120-L128
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PartialStableMatching.lean#L120-L128

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_PartialStableMatching
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*}

theorem TunnellMap.GloballyRanked.existsUnique_partialStable [LinearOrder K] [Fintype S] [Fintype T]
    (I : GloballyRanked K S T) (hcard : Fintype.card S = Fintype.card T) :
    ∃! M : PartialEquiv S T, I.PartialStable M := by sorry
