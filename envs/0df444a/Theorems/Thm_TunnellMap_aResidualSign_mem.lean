-- Prove2me | Theorems.Thm_TunnellMap_aResidualSign_mem
-- name    : TunnellMap.aResidualSign_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:08:34.670018+00:00
-- url     : https://prove2.me/theorems/fb16948a-f07c-573d-82e1-becc7abf9046
-- title:
--   Tunnell Map: a Residual Sign mem
-- statement:
--   The Tunnell Map construction uses the a Residual Sign mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L219-L221
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L219-L221

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.aResidualSign_mem {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    aResidualSign hnpos y = 1 ∨ aResidualSign hnpos y = -1 := by sorry
