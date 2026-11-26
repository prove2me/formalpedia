-- Prove2me | Theorems.Thm_Sendov_pev_Nmom97_46
-- name    : Sendov.pev_Nmom97_46
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:05:33.535092+00:00
-- url     : https://prove2.me/theorems/ee4929fb-eade-4c92-98d2-9ba9234fca9a
-- title:
--   Sendov: pev Nmom97 46
-- statement:
--   The Sendov construction uses the pev Nmom97 46 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree97Packed.lean#L36-L50
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree97Packed.lean#L36-L50

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree97Packed
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov

theorem Sendov.pev_Nmom97_46 (α : ℝ) :
    pev Nmom97_46 α = pev (wsum L97_46 0 (qrow (gg0 97) (gg1 97) (gg2 97) 46)) α := by sorry
