-- Prove2me | Theorems.Thm_TunnellMap_odd_y_of_bOdd
-- name    : TunnellMap.odd_y_of_bOdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:20.617822+00:00
-- url     : https://prove2.me/theorems/5237ff5d-e79c-50ec-ac18-b6222e765a91
-- title:
--   Tunnell Map: odd y of b Odd
-- statement:
--   The Tunnell Map construction uses the odd y of b Odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L16-L29
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L16-L29

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.odd_y_of_bOdd {n : ℤ} (hn : Odd n) (p : BOddRep n) : Odd p.1.y := by sorry
