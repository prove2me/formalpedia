-- Prove2me | Theorems.Thm_TunnellMap_canonicalTargetLift_eq
-- name    : TunnellMap.canonicalTargetLift_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:48:13.196219+00:00
-- url     : https://prove2.me/theorems/4a491f5c-375e-43d5-ac1f-80ffff6e5d63
-- title:
--   Tunnell Map: canonical Target Lift eq
-- statement:
--   The coordinate-level canonical representative agrees with the quotient
--   level one.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L148-L172
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L148-L172

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.canonicalTargetLift_eq {n : ℤ} (hnpos : 0 < n) (t : AResidual n) :
    canonicalTargetLift (residualTargetLift t) =
      residualTargetLift (canonicalAResidualRepresentative hnpos
        ((aResidualInvolution n hnpos).orbit t)) := by sorry
