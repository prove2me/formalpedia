-- Prove2me | Theorems.Thm_TunnellMap_representativeEdgeKey_source_orbit_injective
-- name    : TunnellMap.representativeEdgeKey_source_orbit_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:26:58.38872+00:00
-- url     : https://prove2.me/theorems/7d586f2e-713c-4d47-9b39-1dc111a4ab77
-- title:
--   Tunnell Map: representative Edge Key source orbit injective
-- statement:
--   At a fixed residual source, equal preferred keys determine the target
--   orbit.  This is the source half of Proposition 4.2.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L437-L487
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L437-L487

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.representativeEdgeKey_source_orbit_injective {n : ℤ}
    (hnpos : 0 < n) (s : BResidual n) {t₁ t₂ : AResidual n}
    (hkey : representativeEdgeKey s t₁ = representativeEdgeKey s t₂) :
    (aResidualInvolution n hnpos).orbit t₁ =
      (aResidualInvolution n hnpos).orbit t₂ := by sorry
