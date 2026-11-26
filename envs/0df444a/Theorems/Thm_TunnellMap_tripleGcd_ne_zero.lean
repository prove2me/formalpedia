-- Prove2me | Theorems.Thm_TunnellMap_tripleGcd_ne_zero
-- name    : TunnellMap.tripleGcd_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:40.437131+00:00
-- url     : https://prove2.me/theorems/ab29c62c-9406-5be0-9abc-d2e7d3ad62ba
-- title:
--   Tunnell Map: triple Gcd ne zero
-- statement:
--   The Tunnell Map construction uses the triple Gcd ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L74-L76
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableDirection.lean#L74-L76

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ComputableDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.tripleGcd_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) : tripleGcd v ≠ 0 := by sorry
