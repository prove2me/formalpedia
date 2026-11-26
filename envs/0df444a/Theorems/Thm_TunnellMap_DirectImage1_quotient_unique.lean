-- Prove2me | Theorems.Thm_TunnellMap_DirectImage1_quotient_unique
-- name    : TunnellMap.DirectImage1.quotient_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:39.226747+00:00
-- url     : https://prove2.me/theorems/f86dd0b0-daca-4bf2-a885-76b11c7925a5
-- title:
--   Direct Image1: quotient unique
-- statement:
--   The Direct Image1 construction uses the quotient unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L145-L148
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L145-L148

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.DirectImage1.quotient_unique {n : ℤ} (p : DirectImage1 n)
    {q : ℤ} (hq : p.rep.1.x + 4 * p.rep.1.z - p.rep.1.y = 4 * q) :
    q = p.quotient := by sorry
