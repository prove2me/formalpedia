-- Prove2me | Theorems.Thm_Sendov_wsum_cons
-- name    : Sendov.wsum_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:01:45.84181+00:00
-- url     : https://prove2.me/theorems/afe3bfec-9687-47bc-a8a2-5bd1c09e06d7
-- title:
--   Sendov: wsum cons
-- statement:
--   The Sendov construction uses the wsum cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L100-L102
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L100-L102

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.wsum_cons (L : ℤ) (i : ℕ) (p : List ℤ) (r : List (List ℤ)) :
    wsum L i (p :: r)
      = padd (p.map (fun c => (L / ((i : ℤ) + 4)) * c)) (wsum L (i + 1) r) := by sorry

attribute [defeq] Sendov.wsum_cons
