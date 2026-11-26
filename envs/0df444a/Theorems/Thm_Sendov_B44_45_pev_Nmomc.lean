-- Prove2me | Theorems.Thm_Sendov_B44_45_pev_Nmomc
-- name    : Sendov.B44_45.pev_Nmomc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:20:14.52238+00:00
-- url     : https://prove2.me/theorems/488ea84a-9f45-58d7-af35-cb2c94764788
-- title:
--   B44 45: pev Nmomc
-- statement:
--   The B44 45 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree44_45.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree44_45.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree44_45
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B44_45

theorem Sendov.B44_45.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 44) (gg1 44) (gg2 44) 20)) α := by sorry
