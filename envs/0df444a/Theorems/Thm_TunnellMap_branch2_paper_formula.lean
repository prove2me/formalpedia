-- Prove2me | Theorems.Thm_TunnellMap_branch2_paper_formula
-- name    : TunnellMap.branch2_paper_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:46.8478+00:00
-- url     : https://prove2.me/theorems/cf942f06-0a00-4b9a-880e-540b58dba010
-- title:
--   Tunnell Map: branch2 paper formula
-- statement:
--   The Tunnell Map construction uses the branch2 paper formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L319-L330
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L319-L330

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.branch2_paper_formula {n : ℤ} (p : DirectDomain2 n) :
    2 * (branch2Equiv n p).rep.1.x =
        p.rep.1.x - 2 * p.rep.1.z + p.rep.1.y ∧
      (branch2Equiv n p).rep.1.y = -p.rep.1.x - 2 * p.rep.1.z ∧
      8 * (branch2Equiv n p).rep.1.z =
        p.rep.1.y - p.rep.1.x + 2 * p.rep.1.z := by sorry
