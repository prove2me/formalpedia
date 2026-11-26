-- Prove2me | Theorems.Thm_TunnellMap_tripleGcd_vsmul_pos
-- name    : TunnellMap.tripleGcd_vsmul_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:29.04863+00:00
-- url     : https://prove2.me/theorems/688941de-59d8-4ba8-9139-fe8a851a67b1
-- title:
--   Tunnell Map: triple Gcd vsmul pos
-- statement:
--   The Tunnell Map construction uses the triple Gcd vsmul pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L153-L158
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L153-L158

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.tripleGcd_vsmul_pos {c : ℤ} (hc : 0 < c) (v : Triple) :
    tripleGcd (vsmul c v) = c * tripleGcd v := by sorry
