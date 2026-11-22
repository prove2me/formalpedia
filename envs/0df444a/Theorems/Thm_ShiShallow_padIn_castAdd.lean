-- Prove2me | Theorems.Thm_ShiShallow_padIn_castAdd
-- name    : ShiShallow.padIn_castAdd
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:25:31.275326+00:00
-- url     : https://prove2.me/theorems/9af92d1d-774f-4568-8984-0ae310d4e76b
-- title:
--   Padded input agrees with x on input wires
-- statement:
--   The padded input string restricted to an input wire returns the corresponding bit of x.
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

section
open ShiShallow

theorem ShiShallow.padIn_castAdd {n m : ℕ} (x : Bits n) (i : Fin n) :
    padIn (m := m) x (Fin.castAdd m i) = x i := by sorry

end
