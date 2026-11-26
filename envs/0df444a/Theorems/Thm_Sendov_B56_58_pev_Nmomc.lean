-- Prove2me | Theorems.Thm_Sendov_B56_58_pev_Nmomc
-- name    : Sendov.B56_58.pev_Nmomc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:30:29.816028+00:00
-- url     : https://prove2.me/theorems/3f36dd92-9e60-402c-a482-a56bcb36dc9b
-- title:
--   B56 58: pev Nmomc
-- statement:
--   The B56 58 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree56_58.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree56_58.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree56_58
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B56_58

theorem Sendov.B56_58.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 56) (gg1 56) (gg2 56) 26)) α := by sorry
