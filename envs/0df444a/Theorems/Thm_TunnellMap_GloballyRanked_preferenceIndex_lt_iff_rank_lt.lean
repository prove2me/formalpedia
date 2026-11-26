-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_preferenceIndex_lt_iff_rank_lt
-- name    : TunnellMap.GloballyRanked.preferenceIndex_lt_iff_rank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:00:09.645869+00:00
-- url     : https://prove2.me/theorems/9324066f-eed5-57c8-a759-06b7cc0de1bb
-- title:
--   Globally Ranked: preference Index lt iff rank lt
-- statement:
--   Strict key order is exactly strict position order in a preference list.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean#L40-L60
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean#L40-L60

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_PreferenceListPosition
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.preferenceIndex_lt_iff_rank_lt (I : GloballyRanked K S T)
    (s : S) (t u : T) :
    I.preferenceIndex s t < I.preferenceIndex s u ↔
      I.rank s t < I.rank s u := by sorry
