-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
-- name    : TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:13.452642+00:00
-- url     : https://prove2.me/theorems/a1e6fff9-6660-5ba4-b112-6d9f4d65badd
-- title:
--   Globally Ranked: final Partner mem proposal Targets
-- statement:
--   The Globally Ranked construction uses the final Partner mem proposal Targets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L63-L65
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L63-L65

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : M s ∈ I.proposalTargets M s := by sorry
