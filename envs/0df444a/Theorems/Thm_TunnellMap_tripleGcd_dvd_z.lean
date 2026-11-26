-- Prove2me | Theorems.Thm_TunnellMap_tripleGcd_dvd_z
-- name    : TunnellMap.tripleGcd_dvd_z
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:29.37022+00:00
-- url     : https://prove2.me/theorems/87803d60-1325-4cee-9e98-3f4199273fc7
-- title:
--   Tunnell Map: triple Gcd dvd z
-- statement:
--   The Tunnell Map construction uses the triple Gcd dvd z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L51-L51
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L51-L51

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.tripleGcd_dvd_z (v : Triple) : tripleGcd v ∣ v.z := by sorry
