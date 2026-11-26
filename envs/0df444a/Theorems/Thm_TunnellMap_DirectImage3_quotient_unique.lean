-- Prove2me | Theorems.Thm_TunnellMap_DirectImage3_quotient_unique
-- name    : TunnellMap.DirectImage3.quotient_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:21.504118+00:00
-- url     : https://prove2.me/theorems/0aa57a50-7e65-4f70-afb6-f09ce86fc1a2
-- title:
--   Direct Image3: quotient unique
-- statement:
--   The Direct Image3 construction uses the quotient unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L155-L157
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L155-L157

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.DirectImage3.quotient_unique {n : ℤ} (p : DirectImage3 n)
    {q : ℤ} (hq : p.rep.1.x = 2 * q) : q = p.quotient := by sorry
