-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_deferredAcceptance_output_unique
-- name    : TunnellMap.GloballyRanked.deferredAcceptance_output_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:09.752996+00:00
-- url     : https://prove2.me/theorems/a8f43ec3-f623-492d-8e8b-afd6759808e9
-- title:
--   Globally Ranked: deferred Acceptance output unique
-- statement:
--   Any perfect matching returned with the terminal deferred-acceptance
--   certificate is the unique stable matching.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L94-L100
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L94-L100

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_exists_unique_stable

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.deferredAcceptance_output_unique (I : GloballyRanked K S T)
    (hcard : Fintype.card S = Fintype.card T)
    (M : S ≃ T) (hM : I.DeferredAcceptanceCertificate M) :
    M = Classical.choose (I.exists_unique_stable hcard) := by sorry
