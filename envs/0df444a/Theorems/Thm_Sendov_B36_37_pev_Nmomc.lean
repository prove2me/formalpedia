-- Prove2me | Theorems.Thm_Sendov_B36_37_pev_Nmomc
-- name    : Sendov.B36_37.pev_Nmomc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:15:15.813391+00:00
-- url     : https://prove2.me/theorems/19b14faa-4d31-5b8e-aa1c-631842e0bcc3
-- title:
--   B36 37: pev Nmomc
-- statement:
--   The B36 37 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37

theorem Sendov.B36_37.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 36) (gg1 36) (gg2 36) 16)) α := by sorry
