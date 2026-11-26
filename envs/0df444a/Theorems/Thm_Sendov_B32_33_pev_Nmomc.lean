-- Prove2me | Theorems.Thm_Sendov_B32_33_pev_Nmomc
-- name    : Sendov.B32_33.pev_Nmomc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:14:13.544456+00:00
-- url     : https://prove2.me/theorems/ba5c95c1-265d-4860-8e83-cc4d0ecb15b1
-- title:
--   B32 33: pev Nmomc
-- statement:
--   The B32 33 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree32_33.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree32_33.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33

theorem Sendov.B32_33.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 32) (gg1 32) (gg2 32) 14)) α := by sorry
