-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_le_card
-- name    : TunnellMap.GloballyRanked.proposalCount_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:50.897682+00:00
-- url     : https://prove2.me/theorems/b8bd0fa7-5746-571e-9e6b-abd197c21744
-- title:
--   Globally Ranked: proposal Count le card
-- statement:
--   No source proposes twice to one target, and its total number of proposals
--   is at most the size of the target side.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L78-L81
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L78-L81

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.proposalCount_le_card (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : I.proposalCount M s ≤ Fintype.card T := by sorry
