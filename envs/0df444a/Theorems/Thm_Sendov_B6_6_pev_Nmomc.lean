-- Prove2me | Theorems.Thm_Sendov_B6_6_pev_Nmomc
-- name    : Sendov.B6_6.pev_Nmomc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:05:59.233912+00:00
-- url     : https://prove2.me/theorems/c5f65fe8-b68e-4cfd-9c7b-6a6a9572b4fd
-- title:
--   B6 6: pev Nmomc
-- statement:
--   The B6 6 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6

theorem Sendov.B6_6.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 6) (gg1 6) (gg2 6) 1)) α := by sorry
