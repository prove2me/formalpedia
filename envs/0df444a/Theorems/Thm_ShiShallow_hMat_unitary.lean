-- Prove2me | Theorems.Thm_ShiShallow_hMat_unitary
-- name    : ShiShallow.hMat_unitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:06:43.615067+00:00
-- url     : https://prove2.me/theorems/e451567b-b608-44c7-aa6f-dfbfa61ecd84
-- title:
--   The Hadamard matrix is unitary
-- statement:
--   The 2x2 Hadamard matrix satisfies Hᴴ H = 1.
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
import Theorems.Thm_ShiShallow_inv_sqrt_two_mul_self

section
open ShiShallow

theorem ShiShallow.hMat_unitary : hMat.conjTranspose * hMat = 1 := by sorry

end
