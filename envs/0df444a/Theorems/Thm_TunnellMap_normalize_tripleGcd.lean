-- Prove2me | Theorems.Thm_TunnellMap_normalize_tripleGcd
-- name    : TunnellMap.normalize_tripleGcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:10.884098+00:00
-- url     : https://prove2.me/theorems/397ac204-8041-4c3c-bf85-2cb520e8c695
-- title:
--   Tunnell Map: normalize triple Gcd
-- statement:
--   The Tunnell Map construction uses the normalize triple Gcd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L53-L54
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L53-L54

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.normalize_tripleGcd (v : Triple) : normalize (tripleGcd v) = tripleGcd v := by sorry
