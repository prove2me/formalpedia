-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_pairwise
-- name    : TunnellMap.GloballyRanked.preferenceList_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:49.231806+00:00
-- url     : https://prove2.me/theorems/aa5dd426-7297-4b57-88d6-60e650fef9c2
-- title:
--   Globally Ranked: preference List pairwise
-- statement:
--   The Globally Ranked construction uses the preference List pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean#L20-L23
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean#L20-L23

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_PreferenceList
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]

theorem TunnellMap.GloballyRanked.preferenceList_pairwise (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).Pairwise fun t₁ t₂ => I.rank s t₁ ≤ I.rank s t₂ := by sorry
