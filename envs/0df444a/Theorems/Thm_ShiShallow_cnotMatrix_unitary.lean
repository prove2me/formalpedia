-- Prove2me | Theorems.Thm_ShiShallow_cnotMatrix_unitary
-- name    : ShiShallow.cnotMatrix_unitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:09:11.710184+00:00
-- url     : https://prove2.me/theorems/92f61b4c-c879-44da-b399-de29e48fbdb5
-- title:
--   CNOT is unitary
-- statement:
--   The CNOT operator on n wires is unitary, because it is the permutation matrix of an involution of basis strings.
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
import Theorems.Thm_ShiShallow_cnotMatrix_apply

section
open ShiShallow

theorem ShiShallow.cnotMatrix_unitary {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (cnotMatrix i j).conjTranspose * cnotMatrix i j = 1 := by sorry

end
