-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_preferenceList_strict
-- name    : TunnellMap.GloballyRanked.preferenceList_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:52:14.095803+00:00
-- url     : https://prove2.me/theorems/14593162-40f1-5fd7-94bc-56d4c8bf4008
-- title:
--   Globally Ranked: preference List strict
-- statement:
--   Incident keys occur in strictly increasing order in the generated
--   preference list.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean#L46-L56
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceList.lean#L46-L56

import Definitions.Def_TunnellMap_GloballyRanked
import Definitions.Def_TunnellMap_PreferenceList
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]

theorem TunnellMap.GloballyRanked.preferenceList_strict (I : GloballyRanked K S T) (s : S)
    {i j : Fin (I.preferenceList s).length} (hij : i < j) :
    I.rank s ((I.preferenceList s).get i) <
      I.rank s ((I.preferenceList s).get j) := by sorry
