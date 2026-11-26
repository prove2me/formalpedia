-- Prove2me | Theorems.Thm_TunnellMap_branch3_paper_formula
-- name    : TunnellMap.branch3_paper_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:41:53.605576+00:00
-- url     : https://prove2.me/theorems/3072bad4-0444-4c5f-aec8-d38ac096680c
-- title:
--   Tunnell Map: branch3 paper formula
-- statement:
--   The Tunnell Map construction uses the branch3 paper formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L388-L395
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/QuarterTurns.lean#L388-L395

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.branch3_paper_formula {n : ℤ} (p : DirectDomain3 n) :
    (branch3Equiv n p).rep.1 =
      ⟨2 * p.rep.1.z, p.rep.1.y, -(p.rep.1.x / 4)⟩ := by sorry
