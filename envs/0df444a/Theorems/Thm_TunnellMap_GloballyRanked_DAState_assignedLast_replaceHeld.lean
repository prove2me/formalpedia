-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_replaceHeld
-- name    : TunnellMap.GloballyRanked.DAState.assignedLast_replaceHeld
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:01:42.704047+00:00
-- url     : https://prove2.me/theorems/69a325ad-01fa-53ca-b922-f174fae914bb
-- title:
--   DAState: assigned Last replace Held
-- statement:
--   The DAState construction uses the assigned Last replace Held property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L70-L105
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L70-L105

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.assignedLast_replaceHeld (st : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) (old : S)
    (hheld : st.held (st.nextTarget I s h) = some old) :
    (st.replaceHeld I s rest h old).AssignedLast I := by sorry
