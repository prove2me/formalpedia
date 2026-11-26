-- Prove2me | Theorems.Thm_TunnellMap_residualTarget_decomposition
-- name    : TunnellMap.residualTarget_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:11:43.681736+00:00
-- url     : https://prove2.me/theorems/c56eefb4-9b53-4ffa-a8a6-2e044b2a9efc
-- title:
--   Tunnell Map: residual Target decomposition
-- statement:
--   The coordinate-level sign of a lifted residual target is the sign of the
--   point relative to the canonical representative of its orbit.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L284-L301
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L284-L301

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.residualTarget_decomposition {n : ℤ} (hnpos : 0 < n) (y : AResidual n) :
    signActA hnpos (targetLiftSign (residualTargetLift y))
        (canonicalAResidualRepresentative hnpos
          ((aResidualInvolution n hnpos).orbit y)) = y := by sorry
