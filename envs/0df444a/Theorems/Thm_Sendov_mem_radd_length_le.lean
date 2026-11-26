-- Prove2me | Theorems.Thm_Sendov_mem_radd_length_le
-- name    : Sendov.mem_radd_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:05:11.494885+00:00
-- url     : https://prove2.me/theorems/ef72725c-a6cd-4a5a-a9ac-e071898cba0c
-- title:
--   Sendov: mem radd length le
-- statement:
--   The Sendov construction uses the mem radd length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L433-L451
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L433-L451

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.mem_radd_length_le {m : ℕ} : ∀ (r s : List (List ℤ)),
    (∀ p ∈ r, p.length ≤ m) → (∀ q ∈ s, q.length ≤ m) →
    ∀ x ∈ radd r s, x.length ≤ m := by sorry
