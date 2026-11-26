-- Prove2me | Theorems.Thm_Sendov_B16_18_pev_Nmomc
-- name    : Sendov.B16_18.pev_Nmomc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:07:31.732437+00:00
-- url     : https://prove2.me/theorems/da241446-d0ce-56b2-ab3e-507965871b3f
-- title:
--   B16 18: pev Nmomc
-- statement:
--   The B16 18 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18

theorem Sendov.B16_18.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 16) (gg1 16) (gg2 16) 6)) α := by sorry
