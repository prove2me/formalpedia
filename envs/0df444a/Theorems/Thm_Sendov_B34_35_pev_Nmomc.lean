-- Prove2me | Theorems.Thm_Sendov_B34_35_pev_Nmomc
-- name    : Sendov.B34_35.pev_Nmomc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:14:33.335496+00:00
-- url     : https://prove2.me/theorems/24fe7eb6-4ab0-5c40-a7ea-a327cfe3ae23
-- title:
--   B34 35: pev Nmomc
-- statement:
--   The B34 35 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree34_35.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree34_35.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree34_35
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B34_35

theorem Sendov.B34_35.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 34) (gg1 34) (gg2 34) 15)) α := by sorry
