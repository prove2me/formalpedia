-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
-- name    : TunnellMap.GloballyRanked.mem_preferenceList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:04.439256+00:00
-- url     : https://prove2.me/theorems/2f25ea5a-8409-4fc3-b9fa-11ae00824fb4
-- title:
--   Globally Ranked: mem preference List
-- statement:
--   The Globally Ranked construction uses the mem preference List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean#L30-L35
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean#L30-L35

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_PreferenceList
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]

theorem TunnellMap.GloballyRanked.mem_preferenceList (I : GloballyRanked K S T) (s : S) (t : T) :
    t ∈ I.preferenceList s := by sorry
