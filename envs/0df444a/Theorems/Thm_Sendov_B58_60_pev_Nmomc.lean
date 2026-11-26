-- Prove2me | Theorems.Thm_Sendov_B58_60_pev_Nmomc
-- name    : Sendov.B58_60.pev_Nmomc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:33:00.510524+00:00
-- url     : https://prove2.me/theorems/eac6f0ec-da7b-45c8-af5d-ade12dac666e
-- title:
--   B58 60: pev Nmomc
-- statement:
--   The B58 60 construction uses the pev Nmomc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree58_60.lean#L63-L77
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree58_60.lean#L63-L77

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60

theorem Sendov.B58_60.pev_Nmomc (α : ℝ) :
    pev Nmomc α = pev (wsum Lc 0 (qrow (gg0 58) (gg1 58) (gg2 58) 27)) α := by sorry
