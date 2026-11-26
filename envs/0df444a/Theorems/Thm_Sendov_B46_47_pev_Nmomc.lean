-- Prove2me | Theorems.Thm_Sendov_B46_47_pev_Nmomc
-- name    : Sendov.B46_47.pev_Nmomc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:21:09.107435+00:00
-- url     : https://prove2.me/theorems/9ad580ba-177d-4489-ad80-8827f7a42b41
-- title:
--   B46 47: pev Nmomc
-- statement:
--   The B46 47 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47

theorem Sendov.B46_47.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 46) (gg1 46) (gg2 46) 21)) α := by sorry
