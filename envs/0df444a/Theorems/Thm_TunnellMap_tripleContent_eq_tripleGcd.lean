-- Prove2me | Theorems.Thm_TunnellMap_tripleContent_eq_tripleGcd
-- name    : TunnellMap.tripleContent_eq_tripleGcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:52.929567+00:00
-- url     : https://prove2.me/theorems/18061476-72d0-5814-8beb-8cf8033da19e
-- title:
--   Tunnell Map: triple Content eq triple Gcd
-- statement:
--   The polynomial content used in the specification is the coordinate gcd.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L57-L72
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L57-L72

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.tripleContent_eq_tripleGcd (v : Triple) : tripleContent v = tripleGcd v := by sorry
