-- Prove2me | Theorems.Thm_TunnellMap_representativeEdgeKey_target_orbit_injective
-- name    : TunnellMap.representativeEdgeKey_target_orbit_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:59.894046+00:00
-- url     : https://prove2.me/theorems/bcf4549d-8de2-52a1-b1a2-0a0d0980f137
-- title:
--   Tunnell Map: representative Edge Key target orbit injective
-- statement:
--   At a fixed residual target, equal preferred keys determine the source
--   orbit.  Together with the source statement this proves Proposition 4.2.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L519-L548
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L519-L548

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.representativeEdgeKey_target_orbit_injective {n : ℤ}
    (t : AResidual n) {s₁ s₂ : BResidual n}
    (hkey : representativeEdgeKey s₁ t = representativeEdgeKey s₂ t) :
    (bResidualInvolution n).orbit s₁ = (bResidualInvolution n).orbit s₂ := by sorry
