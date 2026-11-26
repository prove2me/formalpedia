-- Prove2me | Theorems.Thm_TunnellMap_DirectDomain1_quotient_unique
-- name    : TunnellMap.DirectDomain1.quotient_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:51.186638+00:00
-- url     : https://prove2.me/theorems/de472941-95d5-4cbb-be64-593fd0763212
-- title:
--   Direct Domain1: quotient unique
-- statement:
--   The Direct Domain1 construction uses the quotient unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L131-L134
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L131-L134

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.DirectDomain1.quotient_unique {n : ℤ} (p : DirectDomain1 n)
    {q : ℤ} (hq : p.rep.1.x + 2 * p.rep.1.z + p.rep.1.y = 8 * q) :
    q = p.quotient := by sorry
