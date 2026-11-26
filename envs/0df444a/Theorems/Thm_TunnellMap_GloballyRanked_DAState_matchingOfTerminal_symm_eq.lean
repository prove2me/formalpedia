-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_symm_eq
-- name    : TunnellMap.GloballyRanked.DAState.matchingOfTerminal_symm_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:32:31.861713+00:00
-- url     : https://prove2.me/theorems/e60b21b8-2edb-4446-b711-d116ff51a7b8
-- title:
--   DAState: matching Of Terminal symm eq
-- statement:
--   The DAState construction uses the matching Of Terminal symm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceOutput.lean#L89-L96
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceOutput.lean#L89-L96

import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.matchingOfTerminal_symm_eq
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = [])
    (s : S) (t : T) (hheld : st.held t = some s) :
    (matchingOfTerminal I hcard st hv hqueue).symm t = s := by sorry
