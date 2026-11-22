-- Prove2me | Theorems.Thm_ShiShallow_padIn_natAdd
-- name    : ShiShallow.padIn_natAdd
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:25:55.091719+00:00
-- url     : https://prove2.me/theorems/e25c7e43-e07e-4149-a18e-a1724b452885
-- title:
--   Padded input is zero on ancillas
-- statement:
--   The padded input string is false on every ancilla wire.
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

theorem ShiShallow.padIn_natAdd {n m : ℕ} (x : Bits n) (j : Fin m) :
    padIn (m := m) x (Fin.natAdd n j) = false := by sorry

end
