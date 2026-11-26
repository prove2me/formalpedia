-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_preferredToEarlier_injective
-- name    : TunnellMap.GloballyRanked.preferredToEarlier_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:25.639555+00:00
-- url     : https://prove2.me/theorems/f75311b6-8ed0-596b-912a-69fd1c2afae7
-- title:
--   Globally Ranked: preferred To Earlier injective
-- statement:
--   The Globally Ranked construction uses the preferred To Earlier injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Parking.lean#L52-L57
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Parking.lean#L52-L57

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
omit [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.preferredToEarlier_injective (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) (s : S) :
    Function.Injective (I.preferredToEarlier M hM s) := by sorry
