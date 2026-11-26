-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_eq_preferenceIndex_add_one
-- name    : TunnellMap.GloballyRanked.proposalCount_eq_preferenceIndex_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:00:51.530806+00:00
-- url     : https://prove2.me/theorems/8083e230-cd86-4161-bf6b-2ef171f40d80
-- title:
--   Globally Ranked: proposal Count eq preference Index add one
-- statement:
--   The manuscript's equivalence between actual proposal count and one-based
--   preference-list position.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean#L107-L110
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean#L107-L110

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_PreferenceListPosition
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.proposalCount_eq_preferenceIndex_add_one
    (I : GloballyRanked K S T) (M : S ≃ T) (s : S) :
    I.proposalCount M s = (I.preferenceIndex s (M s)).1 + 1 := by sorry
