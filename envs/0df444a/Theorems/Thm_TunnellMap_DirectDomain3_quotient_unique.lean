-- Prove2me | Theorems.Thm_TunnellMap_DirectDomain3_quotient_unique
-- name    : TunnellMap.DirectDomain3.quotient_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:39:45.693334+00:00
-- url     : https://prove2.me/theorems/47b29443-3f43-4519-b8b2-68d22bd36b49
-- title:
--   Direct Domain3: quotient unique
-- statement:
--   The Direct Domain3 construction uses the quotient unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L141-L143
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L141-L143

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.DirectDomain3.quotient_unique {n : ℤ} (p : DirectDomain3 n)
    {q : ℤ} (hq : p.rep.1.x = 4 * q) : q = p.quotient := by sorry
