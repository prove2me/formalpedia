-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_earlierMatchedSources_card_le_position
-- name    : TunnellMap.GloballyRanked.earlierMatchedSources_card_le_position
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:51.557803+00:00
-- url     : https://prove2.me/theorems/04143392-3c40-4b0b-97f7-3f2d22548f56
-- title:
--   Globally Ranked: earlier Matched Sources card le position
-- statement:
--   The Globally Ranked construction uses the earlier Matched Sources card le position property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Parking.lean#L79-L95
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Parking.lean#L79-L95

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
omit [Fintype T] [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.earlierMatchedSources_card_le_position (I : GloballyRanked K S T)
    (M : S ≃ T) (order : Fin (Fintype.card S) ≃ S)
    (horder : I.MatchedKeyOrder M order) (i : Fin (Fintype.card S)) :
    (I.earlierMatchedSources M (order i)).card ≤ i.1 := by sorry
