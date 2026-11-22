-- Prove2me | Theorems.Thm_ShiShallow_inputState_eq_indicator
-- name    : ShiShallow.inputState_eq_indicator
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:10:54.725297+00:00
-- url     : https://prove2.me/theorems/be78989d-cdd1-4abd-b521-c58f4243ff6c
-- title:
--   The input state is a basis indicator
-- statement:
--   The input state is the indicator function of the single basis string padIn x.
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
import Theorems.Thm_ShiShallow_padIn_castAdd
import Theorems.Thm_ShiShallow_padIn_natAdd

section
open ShiShallow

theorem ShiShallow.inputState_eq_indicator {n m : ℕ} (x : Bits n) (y : Bits (n + m)) :
    inputState (m := m) x y = if y = padIn x then 1 else 0 := by sorry

end
