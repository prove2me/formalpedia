-- Prove2me | Theorems.Thm_Sendov_B64_69_pev_Nmomc
-- name    : Sendov.B64_69.pev_Nmomc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:37:57.664704+00:00
-- url     : https://prove2.me/theorems/f8028e04-ed22-4f48-abb2-3c34ddee271b
-- title:
--   B64 69: pev Nmomc
-- statement:
--   The B64 69 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree64_69.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree64_69.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree64_69
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B64_69

theorem Sendov.B64_69.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 64) (gg1 64) (gg2 64) 30)) α := by sorry
