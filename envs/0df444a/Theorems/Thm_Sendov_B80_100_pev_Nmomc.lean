-- Prove2me | Theorems.Thm_Sendov_B80_100_pev_Nmomc
-- name    : Sendov.B80_100.pev_Nmomc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:00:31.049794+00:00
-- url     : https://prove2.me/theorems/e42ae9a6-13d4-4337-ba75-8c4eca61a59a
-- title:
--   B80 100: pev Nmomc
-- statement:
--   The B80 100 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree80_100.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree80_100
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B80_100

theorem Sendov.B80_100.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 80) (gg1 80) (gg2 80) 38)) α := by sorry
