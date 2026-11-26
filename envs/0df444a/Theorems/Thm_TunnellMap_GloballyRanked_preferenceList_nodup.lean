-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_nodup
-- name    : TunnellMap.GloballyRanked.preferenceList_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:01.079692+00:00
-- url     : https://prove2.me/theorems/4fc9be18-8453-4e65-9a26-12026bfd9815
-- title:
--   Globally Ranked: preference List nodup
-- statement:
--   The Globally Ranked construction uses the preference List nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean#L25-L28
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean#L25-L28

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_PreferenceList
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]

theorem TunnellMap.GloballyRanked.preferenceList_nodup (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).Nodup := by sorry
