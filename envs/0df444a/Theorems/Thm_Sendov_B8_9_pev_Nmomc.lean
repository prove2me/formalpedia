-- Prove2me | Theorems.Thm_Sendov_B8_9_pev_Nmomc
-- name    : Sendov.B8_9.pev_Nmomc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:06:11.864482+00:00
-- url     : https://prove2.me/theorems/f58526bc-ae40-50f3-aacb-3798eba7730a
-- title:
--   B8 9: pev Nmomc
-- statement:
--   The B8 9 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree8_9
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B8_9

theorem Sendov.B8_9.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 8) (gg1 8) (gg2 8) 2)) α := by sorry
