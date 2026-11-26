-- Prove2me | Theorems.Thm_Sendov_B24_26_pev_Nmomc
-- name    : Sendov.B24_26.pev_Nmomc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:09:55.586832+00:00
-- url     : https://prove2.me/theorems/0a71add2-f3eb-43ee-aef9-9056d73f98eb
-- title:
--   B24 26: pev Nmomc
-- statement:
--   The B24 26 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree24_26.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26

theorem Sendov.B24_26.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 24) (gg1 24) (gg2 24) 10)) α := by sorry
