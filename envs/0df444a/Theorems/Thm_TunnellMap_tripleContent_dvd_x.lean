-- Prove2me | Theorems.Thm_TunnellMap_tripleContent_dvd_x
-- name    : TunnellMap.tripleContent_dvd_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:26:15.479188+00:00
-- url     : https://prove2.me/theorems/3c6559f9-229c-5112-b150-59989d8e5c77
-- title:
--   Tunnell Map: triple Content dvd x
-- statement:
--   The Tunnell Map construction uses the triple Content dvd x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L33-L35
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L33-L35

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.tripleContent_dvd_x (v : Triple) : tripleContent v ∣ v.x := by sorry
