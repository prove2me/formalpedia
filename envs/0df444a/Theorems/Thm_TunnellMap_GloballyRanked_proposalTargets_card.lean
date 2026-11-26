-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_proposalTargets_card
-- name    : TunnellMap.GloballyRanked.proposalTargets_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:38.912902+00:00
-- url     : https://prove2.me/theorems/b7525438-5556-4c62-9562-8d9a6e58cb53
-- title:
--   Globally Ranked: proposal Targets card
-- statement:
--   The Globally Ranked construction uses the proposal Targets card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L71-L74
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L71-L74

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.proposalTargets_card (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) :
    (I.proposalTargets M s).card = I.proposalCount M s := by sorry
