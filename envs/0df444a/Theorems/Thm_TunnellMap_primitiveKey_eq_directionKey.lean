-- Prove2me | Theorems.Thm_TunnellMap_primitiveKey_eq_directionKey
-- name    : TunnellMap.primitiveKey_eq_directionKey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:30:35.661937+00:00
-- url     : https://prove2.me/theorems/33d67924-1f95-5811-bffc-e43f1b41a4cb
-- title:
--   Tunnell Map: primitive Key eq direction Key
-- statement:
--   On a primitive, canonically oriented triple the key needs no
--   normalization at all.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L144-L149
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L144-L149

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitiveKey_eq_directionKey {v : Triple}
    (hcontent : tripleGcd v = 1) (horiented : FirstNonzeroPositive v) :
    primitiveKey v = directionKey v := by sorry
