-- Prove2me | Theorems.Thm_Sendov_pevZ_wsum
-- name    : Sendov.pevZ_wsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:42.219426+00:00
-- url     : https://prove2.me/theorems/e4ba29f9-8e9d-5185-8160-6ee0f67450c4
-- title:
--   Sendov: pev Z wsum
-- statement:
--   The packed weighted sum agrees with packing the weighted sum: this is what makes the
--   check a single integer comparison.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L386-L393
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L386-L393

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.pevZ_wsum (L : ℤ) : ∀ (r : List (List ℤ)) (i : ℕ) (β : ℤ),
    pevZ (wsum L i r) β = wsumZ L i (rowZ r β) := by sorry
