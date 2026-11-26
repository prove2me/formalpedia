-- Prove2me | Theorems.Thm_TunnellMap_DirectImage2_quotient_unique
-- name    : TunnellMap.DirectImage2.quotient_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:16.986454+00:00
-- url     : https://prove2.me/theorems/e5b5201b-3166-40af-9377-2d8e89196418
-- title:
--   Direct Image2: quotient unique
-- statement:
--   The Direct Image2 construction uses the quotient unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L150-L153
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L150-L153

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.DirectImage2.quotient_unique {n : ℤ} (p : DirectImage2 n)
    {q : ℤ} (hq : p.rep.1.x - 4 * p.rep.1.z + p.rep.1.y = 4 * q) :
    q = p.quotient := by sorry
