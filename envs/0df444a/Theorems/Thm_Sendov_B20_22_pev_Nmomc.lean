-- Prove2me | Theorems.Thm_Sendov_B20_22_pev_Nmomc
-- name    : Sendov.B20_22.pev_Nmomc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:09:00.033815+00:00
-- url     : https://prove2.me/theorems/26f5cca5-433a-4905-a0e6-3cfa023f69e3
-- title:
--   B20 22: pev Nmomc
-- statement:
--   The B20 22 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22

theorem Sendov.B20_22.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 20) (gg1 20) (gg2 20) 8)) α := by sorry
