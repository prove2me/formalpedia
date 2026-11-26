-- Prove2me | Theorems.Thm_TunnellMap_branch1_paper_formula
-- name    : TunnellMap.branch1_paper_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:54.695704+00:00
-- url     : https://prove2.me/theorems/2a780d73-348d-5d39-8918-3eb372b9e753
-- title:
--   Tunnell Map: branch1 paper formula
-- statement:
--   The Tunnell Map construction uses the branch1 paper formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L230-L241
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L230-L241

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.branch1_paper_formula {n : ℤ} (p : DirectDomain1 n) :
    2 * (branch1Equiv n p).rep.1.x =
        p.rep.1.x + 2 * p.rep.1.z - p.rep.1.y ∧
      (branch1Equiv n p).rep.1.y = p.rep.1.x - 2 * p.rep.1.z ∧
      8 * (branch1Equiv n p).rep.1.z =
        p.rep.1.x + 2 * p.rep.1.z + p.rep.1.y := by sorry
