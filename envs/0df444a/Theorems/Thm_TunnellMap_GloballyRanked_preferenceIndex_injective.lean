-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_preferenceIndex_injective
-- name    : TunnellMap.GloballyRanked.preferenceIndex_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:51:36.139771+00:00
-- url     : https://prove2.me/theorems/9c3a6a8f-1950-49db-9ba4-01e5279a8c0c
-- title:
--   Globally Ranked: preference Index injective
-- statement:
--   The Globally Ranked construction uses the preference Index injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean#L29-L37
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean#L29-L37

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_PreferenceListPosition
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.preferenceIndex_injective (I : GloballyRanked K S T) (s : S) :
    Function.Injective (I.preferenceIndex s) := by sorry
