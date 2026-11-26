-- Prove2me | Theorems.Thm_Sendov_B50_51_pev_Nmomc
-- name    : Sendov.B50_51.pev_Nmomc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:24:13.021583+00:00
-- url     : https://prove2.me/theorems/1fad5e39-5446-5bf4-932a-59863d371d7c
-- title:
--   B50 51: pev Nmomc
-- statement:
--   The B50 51 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree50_51.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree50_51.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51

theorem Sendov.B50_51.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 50) (gg1 50) (gg2 50) 23)) α := by sorry
