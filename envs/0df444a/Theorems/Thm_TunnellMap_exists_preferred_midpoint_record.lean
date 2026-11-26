-- Prove2me | Theorems.Thm_TunnellMap_exists_preferred_midpoint_record
-- name    : TunnellMap.exists_preferred_midpoint_record
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:36.411184+00:00
-- url     : https://prove2.me/theorems/b7d770c7-1c54-5728-a23a-317357d02047
-- title:
--   Tunnell Map: exists preferred midpoint record
-- statement:
--   The complete preferred midpoint record for every residual pair.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointRecord.lean#L111-L132
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointRecord.lean#L111-L132

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_MidpointBound
import Definitions.Def_TunnellMap_MidpointRecord
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.exists_preferred_midpoint_record {n : ℤ} (hn : Odd n)
    (s : BResidual n) (t : AResidual n) :
    Nonempty (PreferredMidpointRecord s t) := by sorry
