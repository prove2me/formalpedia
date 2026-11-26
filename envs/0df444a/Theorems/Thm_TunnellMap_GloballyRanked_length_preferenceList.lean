-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
-- name    : TunnellMap.GloballyRanked.length_preferenceList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:41.807199+00:00
-- url     : https://prove2.me/theorems/6399dcd8-31d2-4793-b93e-b08530f665af
-- title:
--   Globally Ranked: length preference List
-- statement:
--   The Globally Ranked construction uses the length preference List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean#L37-L42
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean#L37-L42

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_PreferenceList
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]

theorem TunnellMap.GloballyRanked.length_preferenceList (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).length = Fintype.card T := by sorry
