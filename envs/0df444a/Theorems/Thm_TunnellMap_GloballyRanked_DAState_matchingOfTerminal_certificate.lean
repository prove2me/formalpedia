-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_certificate
-- name    : TunnellMap.GloballyRanked.DAState.matchingOfTerminal_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:05.786166+00:00
-- url     : https://prove2.me/theorems/4b7e63b9-5def-5b7f-a09e-b5a31d3aab2e
-- title:
--   DAState: matching Of Terminal certificate
-- statement:
--   The matching encoded by a valid terminal state has the transcript-free
--   deferred-acceptance certificate.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L267-L290
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L267-L290

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.matchingOfTerminal_certificate
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hp : st.ProposalValid I)
    (hqueue : st.queue = []) :
    I.DeferredAcceptanceCertificate
      (matchingOfTerminal I hcard st hv hqueue) := by sorry
