-- Prove2me | Theorems.Thm_Sendov_l1row_rscale
-- name    : Sendov.l1row_rscale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:04:33.323257+00:00
-- url     : https://prove2.me/theorems/93c779eb-df76-42c4-a626-011f44330928
-- title:
--   Sendov: l1row rscale
-- statement:
--   The Sendov construction uses the l1row rscale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L224-L231
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L224-L231

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.l1row_rscale (g : List ℤ) (r : List (List ℤ)) :
    l1row (rscale g r) ≤ l1 g * l1row r := by sorry
