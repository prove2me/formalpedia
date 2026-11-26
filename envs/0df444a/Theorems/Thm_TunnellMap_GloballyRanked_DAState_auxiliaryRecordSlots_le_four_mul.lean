-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_auxiliaryRecordSlots_le_four_mul
-- name    : TunnellMap.GloballyRanked.DAState.auxiliaryRecordSlots_le_four_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:48:19.090352+00:00
-- url     : https://prove2.me/theorems/0546159b-8a21-4c21-8dc2-f08fdb28a9bd
-- title:
--   DAState: auxiliary Record Slots le four mul
-- statement:
--   Under equal side cardinalities, a valid state uses at most `4m`
--   auxiliary control records.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L265-L272
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L265-L272

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

theorem TunnellMap.GloballyRanked.DAState.auxiliaryRecordSlots_le_four_mul
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) :
    st.auxiliaryRecordSlots I ≤ 4 * Fintype.card S := by sorry
