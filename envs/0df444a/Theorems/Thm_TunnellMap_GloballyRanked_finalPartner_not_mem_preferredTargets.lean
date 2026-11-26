-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_not_mem_preferredTargets
-- name    : TunnellMap.GloballyRanked.finalPartner_not_mem_preferredTargets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:28.397506+00:00
-- url     : https://prove2.me/theorems/a490a9bc-c832-56e2-a222-a1733f1dcb50
-- title:
--   Globally Ranked: final Partner not mem preferred Targets
-- statement:
--   The Globally Ranked construction uses the final Partner not mem preferred Targets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L67-L69
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptance.lean#L67-L69

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_DeferredAcceptance
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K]
variable [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.finalPartner_not_mem_preferredTargets (I : GloballyRanked K S T)
    (M : S ≃ T) (s : S) : M s ∉ I.preferredTargets M s := by sorry
