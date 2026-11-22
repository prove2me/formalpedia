-- Prove2me | Theorems.Thm_ShiShallow_cnotMatrix_apply
-- name    : ShiShallow.cnotMatrix_apply
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:23:35.641086+00:00
-- url     : https://prove2.me/theorems/219ae7f9-b2ab-4099-a597-c2b30884b1cb
-- title:
--   CNOT's matrix is a permutation matrix
-- statement:
--   The CNOT matrix entry at (w, v) is 1 exactly when v is the image of w under the CNOT bit-flip involution, and 0 otherwise.
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

theorem ShiShallow.cnotMatrix_apply {n : ℕ} (i j : Fin n) (hij : i ≠ j) (w v : Bits n) :
    cnotMatrix i j w v = if v = cnotEquiv i j hij w then 1 else 0 := by sorry

end
