-- Prove2me | Theorems.Thm_Sendov_B60_63_pev_Nmomc
-- name    : Sendov.B60_63.pev_Nmomc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:35:39.955352+00:00
-- url     : https://prove2.me/theorems/efd91153-93d4-4f7f-b716-69bb7d74ffc8
-- title:
--   B60 63: pev Nmomc
-- statement:
--   The B60 63 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree60_63.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree60_63.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree60_63
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B60_63

theorem Sendov.B60_63.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 60) (gg1 60) (gg2 60) 28)) α := by sorry
