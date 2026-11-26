-- Prove2me | Theorems.Thm_TunnellMap_tripleGcd_dvd_x
-- name    : TunnellMap.tripleGcd_dvd_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:00.502543+00:00
-- url     : https://prove2.me/theorems/a50a0579-c70f-4043-8d23-7a082d38f2a4
-- title:
--   Tunnell Map: triple Gcd dvd x
-- statement:
--   The Tunnell Map construction uses the triple Gcd dvd x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L45-L46
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L45-L46

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.tripleGcd_dvd_x (v : Triple) : tripleGcd v ∣ v.x := by sorry
