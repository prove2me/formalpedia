-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_preferredTargets_card_eq_preferenceIndex
-- name    : TunnellMap.GloballyRanked.preferredTargets_card_eq_preferenceIndex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:00:35.437634+00:00
-- url     : https://prove2.me/theorems/590f16b2-10c7-55c4-9fd9-3e5191618324
-- title:
--   Globally Ranked: preferred Targets card eq preference Index
-- statement:
--   The number of preferred targets is the zero-based position of the final
--   target.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean#L64-L103
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PreferenceListPosition.lean#L64-L103

import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_PreferenceListPosition
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.preferredTargets_card_eq_preferenceIndex
    (I : GloballyRanked K S T) (M : S ≃ T) (s : S) :
    (I.preferredTargets M s).card = (I.preferenceIndex s (M s)).1 := by sorry
