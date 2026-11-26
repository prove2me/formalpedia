-- Prove2me | Theorems.Thm_Sendov_Nmom20_eq
-- name    : Sendov.Nmom20_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:05:31.051711+00:00
-- url     : https://prove2.me/theorems/14cf6e19-a24e-58a5-ab6f-c00beb7def55
-- title:
--   Sendov: Nmom20 eq
-- statement:
--   The generator's numerator is the moment numerator.  The computational content is one
--   integer exponentiation and seventeen digit extractions.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20Packed.lean#L40-L48
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20Packed.lean#L40-L48

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20Packed
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 100000
open Sendov

theorem Sendov.Nmom20_eq :
    Nmom20 = wsum L20 0 (qrow (gg0 20) (gg1 20) (gg2 20) 8) := by sorry
