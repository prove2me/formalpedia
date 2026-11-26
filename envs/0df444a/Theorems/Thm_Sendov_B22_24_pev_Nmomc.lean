-- Prove2me | Theorems.Thm_Sendov_B22_24_pev_Nmomc
-- name    : Sendov.B22_24.pev_Nmomc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:09:30.317776+00:00
-- url     : https://prove2.me/theorems/ac1a7431-b1ba-59c7-a160-ab03bb486091
-- title:
--   B22 24: pev Nmomc
-- statement:
--   The B22 24 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree22_24.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24

theorem Sendov.B22_24.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 22) (gg1 22) (gg2 22) 9)) α := by sorry
