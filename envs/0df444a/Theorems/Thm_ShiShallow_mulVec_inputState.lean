-- Prove2me | Theorems.Thm_ShiShallow_mulVec_inputState
-- name    : ShiShallow.mulVec_inputState
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:32:21.429767+00:00
-- url     : https://prove2.me/theorems/e423a375-064f-41db-9013-a05fd860477c
-- title:
--   Applying an operator to a basis state reads off a column
-- statement:
--   Multiplying an operator by the input basis state returns the corresponding column of the operator.
-- source:
--   Original work by Yueheng Shi (Apache-2.0), formalised in Lean 4 with Mathlib. Part of the ShiShallow development on shallow quantum circuits and causal cones.

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open` and the proof is replaced by `sorry`;
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit
import Definitions.Def_ShiShallow_Operator
import Theorems.Thm_ShiShallow_inputState_eq_indicator

section
open ShiShallow

theorem ShiShallow.mulVec_inputState {n m : ℕ} (A : Op (n + m)) (x : Bits n) (y : Bits (n + m)) :
    A.mulVec (inputState x) y = A y (padIn x) := by sorry

end
