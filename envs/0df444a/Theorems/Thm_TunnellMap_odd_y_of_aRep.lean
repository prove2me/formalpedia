-- Prove2me | Theorems.Thm_TunnellMap_odd_y_of_aRep
-- name    : TunnellMap.odd_y_of_aRep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:38.960586+00:00
-- url     : https://prove2.me/theorems/12fb3111-5b7c-4857-8380-3ca06e0e4675
-- title:
--   Tunnell Map: odd y of a Rep
-- statement:
--   The Tunnell Map construction uses the odd y of a Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L31-L44
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L31-L44

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.odd_y_of_aRep {n : ℤ} (hn : Odd n) (p : ARep n) : Odd p.1.y := by sorry
