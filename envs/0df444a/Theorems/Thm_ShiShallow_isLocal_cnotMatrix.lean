-- Prove2me | Theorems.Thm_ShiShallow_isLocal_cnotMatrix
-- name    : ShiShallow.isLocal_cnotMatrix
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:21:25.956059+00:00
-- url     : https://prove2.me/theorems/d8f6866e-bdb1-45b7-929f-9b72cbf62bb3
-- title:
--   CNOT's matrix is local to its two wires
-- statement:
--   The CNOT matrix is {i,j}-local.
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

theorem ShiShallow.isLocal_cnotMatrix {n : ℕ} (i j : Fin n) :
    IsLocal {i, j} (cnotMatrix i j) := by sorry

end
