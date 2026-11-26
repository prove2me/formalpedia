-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_le_earlier_add_one
-- name    : TunnellMap.GloballyRanked.proposalCount_le_earlier_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:46:49.681248+00:00
-- url     : https://prove2.me/theorems/861d2ed9-4be5-468c-b193-0103ba9881f0
-- title:
--   Globally Ranked: proposal Count le earlier add one
-- statement:
--   The pointwise estimate used in the parking-function proof.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Parking.lean#L61-L69
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Parking.lean#L61-L69

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
omit [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.proposalCount_le_earlier_add_one (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) (s : S) :
    I.proposalCount M s ≤ (I.earlierMatchedSources M s).card + 1 := by sorry
