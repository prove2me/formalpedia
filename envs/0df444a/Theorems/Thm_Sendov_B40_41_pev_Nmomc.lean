-- Prove2me | Theorems.Thm_Sendov_B40_41_pev_Nmomc
-- name    : Sendov.B40_41.pev_Nmomc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:18:01.670227+00:00
-- url     : https://prove2.me/theorems/57afee3f-22a6-56ac-9b7d-147ddb86beee
-- title:
--   B40 41: pev Nmomc
-- statement:
--   The B40 41 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree40_41.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41

theorem Sendov.B40_41.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 40) (gg1 40) (gg2 40) 18)) α := by sorry
