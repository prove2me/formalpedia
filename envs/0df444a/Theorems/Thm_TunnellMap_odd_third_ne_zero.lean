-- Prove2me | Theorems.Thm_TunnellMap_odd_third_ne_zero
-- name    : TunnellMap.odd_third_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:43:43.319469+00:00
-- url     : https://prove2.me/theorems/088e3377-58e8-44b6-9937-c8c2ba397112
-- title:
--   Tunnell Map: odd third ne zero
-- statement:
--   The Tunnell Map construction uses the odd third ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L144-L148
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L144-L148

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.odd_third_ne_zero {p : Triple} (hp : Odd p.z) : p ≠ ⟨0, 0, 0⟩ := by sorry
