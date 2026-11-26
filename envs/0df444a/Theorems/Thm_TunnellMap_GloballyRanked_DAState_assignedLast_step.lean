-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_step
-- name    : TunnellMap.GloballyRanked.DAState.assignedLast_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:02:25.347797+00:00
-- url     : https://prove2.me/theorems/c2ae0240-feac-5878-9283-7fe2b23b4d09
-- title:
--   DAState: assigned Last step
-- statement:
--   The DAState construction uses the assigned Last step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L120-L131
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L120-L131

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

theorem TunnellMap.GloballyRanked.DAState.assignedLast_step (st st' : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I)
    (hstep : st.step I = some st') :
    st'.AssignedLast I := by sorry
