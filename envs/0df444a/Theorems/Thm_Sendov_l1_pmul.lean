-- Prove2me | Theorems.Thm_Sendov_l1_pmul
-- name    : Sendov.l1_pmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:04:11.726204+00:00
-- url     : https://prove2.me/theorems/f28625c7-c8d1-4441-ae95-1e7ba7341099
-- title:
--   Sendov: l1 pmul
-- statement:
--   The Sendov construction uses the l1 pmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L184-L195
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L184-L195

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.l1_pmul (p q : List ℤ) : l1 (pmul p q) ≤ l1 p * l1 q := by sorry
