-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_total_le_square
-- name    : TunnellMap.GloballyRanked.proposalCount_total_le_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:14.413443+00:00
-- url     : https://prove2.me/theorems/8e361a9c-2413-5379-8a06-340cad45f105
-- title:
--   Globally Ranked: proposal Count total le square
-- statement:
--   The elementary `m²` termination bound before the parking improvement.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L84-L90
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L84-L90

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.proposalCount_total_le_square (I : GloballyRanked K S T)
    (M : S ≃ T) :
    (∑ s : S, I.proposalCount M s) ≤ Fintype.card S * Fintype.card T := by sorry
