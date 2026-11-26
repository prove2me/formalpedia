-- Prove2me | Theorems.Thm_TunnellMap_aResidual_decomposition
-- name    : TunnellMap.aResidual_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:08:37.81134+00:00
-- url     : https://prove2.me/theorems/f32e455e-f6d5-5633-90f3-c8dc03ebdede
-- title:
--   Tunnell Map: a Residual decomposition
-- statement:
--   The Tunnell Map construction uses the a Residual decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L246-L251
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L246-L251

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.aResidual_decomposition {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    signActA hnpos (aResidualSign hnpos y)
        (canonicalAResidualRepresentative hnpos
          ((aResidualInvolution n hnpos).orbit y)) = y := by sorry
