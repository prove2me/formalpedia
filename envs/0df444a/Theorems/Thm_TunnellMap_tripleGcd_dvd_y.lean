-- Prove2me | Theorems.Thm_TunnellMap_tripleGcd_dvd_y
-- name    : TunnellMap.tripleGcd_dvd_y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:20.518713+00:00
-- url     : https://prove2.me/theorems/5c61232d-16a4-516b-a649-0ff8511cb404
-- title:
--   Tunnell Map: triple Gcd dvd y
-- statement:
--   The Tunnell Map construction uses the triple Gcd dvd y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L48-L49
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L48-L49

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.tripleGcd_dvd_y (v : Triple) : tripleGcd v ∣ v.y := by sorry
