-- Prove2me | Theorems.Thm_Sendov_pev_Nmom97_47
-- name    : Sendov.pev_Nmom97_47
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:05:42.630434+00:00
-- url     : https://prove2.me/theorems/bf9c5eb1-c355-4efb-b340-fc6050433c62
-- title:
--   Sendov: pev Nmom97 47
-- statement:
--   The Sendov construction uses the pev Nmom97 47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree97Packed.lean#L72-L86
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree97Packed.lean#L72-L86

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree97Packed
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov

theorem Sendov.pev_Nmom97_47 (α : ℝ) :
    pev Nmom97_47 α = pev (wsum L97_47 0 (qrow (gg0 97) (gg1 97) (gg2 97) 47)) α := by sorry
