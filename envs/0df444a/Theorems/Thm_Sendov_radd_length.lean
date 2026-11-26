-- Prove2me | Theorems.Thm_Sendov_radd_length
-- name    : Sendov.radd_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:04:49.939948+00:00
-- url     : https://prove2.me/theorems/f8e33ef2-6a1a-46ad-9f9b-18e8bbf08041
-- title:
--   Sendov: radd length
-- statement:
--   The Sendov construction uses the radd length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L268-L275
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L268-L275

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.radd_length (r s : List (List ℤ)) :
    (radd r s).length = max r.length s.length := by sorry
