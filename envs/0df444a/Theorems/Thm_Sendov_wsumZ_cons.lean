-- Prove2me | Theorems.Thm_Sendov_wsumZ_cons
-- name    : Sendov.wsumZ_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:37.497951+00:00
-- url     : https://prove2.me/theorems/17f48c90-b247-543f-936b-8428f75ab24e
-- title:
--   Sendov: wsum Z cons
-- statement:
--   The Sendov construction uses the wsum Z cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L367-L368
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L367-L368

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.wsumZ_cons (L : ℤ) (i : ℕ) (a : ℤ) (s : List ℤ) :
    wsumZ L i (a :: s) = (L / ((i : ℤ) + 4)) * a + wsumZ L (i + 1) s := by sorry

attribute [defeq] Sendov.wsumZ_cons
