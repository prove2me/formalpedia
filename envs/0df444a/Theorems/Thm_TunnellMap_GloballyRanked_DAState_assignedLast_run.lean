-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_run
-- name    : TunnellMap.GloballyRanked.DAState.assignedLast_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:14:35.651026+00:00
-- url     : https://prove2.me/theorems/10bf2c9e-1858-51d3-b298-bdfa5e9b5dc0
-- title:
--   DAState: assigned Last run
-- statement:
--   The DAState construction uses the assigned Last run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L133-L143
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L133-L143

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

theorem TunnellMap.GloballyRanked.DAState.assignedLast_run (st : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I) :
    (st.run I).AssignedLast I := by sorry
