-- Prove2me | Theorems.Thm_Sendov_pev_wsum
-- name    : Sendov.pev_wsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:04:13.21408+00:00
-- url     : https://prove2.me/theorems/90641c36-7af9-414b-94b1-45feedde9596
-- title:
--   Sendov: pev wsum
-- statement:
--   **The scaled moment is an integer polynomial.**  Given that `L` clears every denominator
--   `i+j+4` occurring, `wsum` computes `L` times `Sendov.irow`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L106-L132
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L106-L132

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.pev_wsum (L : ℤ) : ∀ (r : List (List ℤ)) (i : ℕ) (α : ℝ),
    (∀ j, j < r.length → ((i : ℤ) + j + 4) ∣ L) →
    pev (wsum L i r) α = (L : ℝ) * irow r i α := by sorry
