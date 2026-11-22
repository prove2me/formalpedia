-- Prove2me | Theorems.Thm_ShiShallow_inputState_norm
-- name    : ShiShallow.inputState_norm
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:18:18.16709+00:00
-- url     : https://prove2.me/theorems/1493a665-145a-4ab6-bb48-1cdc8c4e4b0f
-- title:
--   The input basis state is normalised
-- statement:
--   The computational-basis input state (x on the input wires, zeros on ancillas) has total squared modulus 1.
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

section
open ShiShallow

theorem ShiShallow.inputState_norm {n m : ℕ} (x : Bits n) :
    ∑ y : Bits (n + m), ‖inputState (m := m) x y‖ ^ 2 = 1 := by sorry

end
