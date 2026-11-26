-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_get_preferenceIndex
-- name    : TunnellMap.GloballyRanked.get_preferenceIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:27.153751+00:00
-- url     : https://prove2.me/theorems/987c7453-d946-4e33-82a7-a18e60a9cf56
-- title:
--   Globally Ranked: get preference Index
-- statement:
--   The Globally Ranked construction uses the get preference Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean#L24-L27
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean#L24-L27

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_PreferenceListPosition
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.get_preferenceIndex (I : GloballyRanked K S T)
    (s : S) (t : T) :
    (I.preferenceList s).get (I.preferenceIndex s t) = t := by sorry
