-- Prove2me | Theorems.Thm_TunnellMap_directionKey_vsmul
-- name    : TunnellMap.directionKey_vsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:30:56.234698+00:00
-- url     : https://prove2.me/theorems/ae5d98b4-f370-4c41-b916-4ef491c73a64
-- title:
--   Tunnell Map: direction Key vsmul
-- statement:
--   The projective key only depends on the rational line of a triple.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L185-L195
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L185-L195

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.directionKey_vsmul {c : ℤ} (hc : c ≠ 0) {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    directionKey (vsmul c v) = directionKey v := by sorry
