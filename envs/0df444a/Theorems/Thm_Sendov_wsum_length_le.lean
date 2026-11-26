-- Prove2me | Theorems.Thm_Sendov_wsum_length_le
-- name    : Sendov.wsum_length_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:03:23.903182+00:00
-- url     : https://prove2.me/theorems/9333e9e9-36fe-5ff1-84b6-2822633ded08
-- title:
--   Sendov: wsum length le
-- statement:
--   The weighted sum is no longer than the entries it combines.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L508-L518
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L508-L518

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.wsum_length_le {m : ℕ} (L : ℤ) : ∀ (r : List (List ℤ)) (i : ℕ),
    (∀ p ∈ r, p.length ≤ m) → (wsum L i r).length ≤ m := by sorry
