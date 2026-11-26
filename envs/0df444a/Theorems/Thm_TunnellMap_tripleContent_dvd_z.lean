-- Prove2me | Theorems.Thm_TunnellMap_tripleContent_dvd_z
-- name    : TunnellMap.tripleContent_dvd_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:11.570795+00:00
-- url     : https://prove2.me/theorems/451aeb2a-05b8-4d8c-92ad-5d41db1ddef3
-- title:
--   Tunnell Map: triple Content dvd z
-- statement:
--   The Tunnell Map construction uses the triple Content dvd z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L41-L43
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L41-L43

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.tripleContent_dvd_z (v : Triple) : tripleContent v ∣ v.z := by sorry
