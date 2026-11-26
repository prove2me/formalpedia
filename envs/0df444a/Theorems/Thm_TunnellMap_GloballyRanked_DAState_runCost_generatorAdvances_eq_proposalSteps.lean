-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_runCost_generatorAdvances_eq_proposalSteps
-- name    : TunnellMap.GloballyRanked.DAState.runCost_generatorAdvances_eq_proposalSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:16:13.53962+00:00
-- url     : https://prove2.me/theorems/2ae9c76a-ac60-4c62-b3a4-94a762f850e9
-- title:
--   DAState: run Cost generator Advances eq proposal Steps
-- statement:
--   Generator advances are exactly the successful proposal-step count.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean#L115-L120
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean#L115-L120

import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Definitions.Def_TunnellMap_ControlCost
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.runCost_generatorAdvances_eq_proposalSteps (st : I.DAState) :
    (st.runCost I).generatorAdvances = st.proposalSteps I := by sorry
