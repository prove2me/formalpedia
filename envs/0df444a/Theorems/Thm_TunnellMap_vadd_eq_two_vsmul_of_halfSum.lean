-- Prove2me | Theorems.Thm_TunnellMap_vadd_eq_two_vsmul_of_halfSum
-- name    : TunnellMap.vadd_eq_two_vsmul_of_halfSum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:47:07.171267+00:00
-- url     : https://prove2.me/theorems/25f7b42a-4d33-42b8-8a2d-fff2fd151fc8
-- title:
--   Tunnell Map: vadd eq two vsmul of half Sum
-- statement:
--   The Tunnell Map construction uses the vadd eq two vsmul of half Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointRecord.lean#L14-L17
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointRecord.lean#L14-L17

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_MidpointBound
import Definitions.Def_TunnellMap_MidpointRecord
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.vadd_eq_two_vsmul_of_halfSum {h E F : Triple}
    (hh : IsHalfSum h E F) : vadd E F = vsmul 2 h := by sorry
