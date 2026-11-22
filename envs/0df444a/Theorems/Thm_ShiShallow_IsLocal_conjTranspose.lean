-- Prove2me | Theorems.Thm_ShiShallow_IsLocal_conjTranspose
-- name    : ShiShallow.IsLocal.conjTranspose
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:23:55.881466+00:00
-- url     : https://prove2.me/theorems/2b8849fd-0f5e-415b-a599-e16d18b225b0
-- title:
--   Locality is preserved by adjoint
-- statement:
--   If A is S-local then so is its conjugate transpose.
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

theorem ShiShallow.IsLocal.conjTranspose {n : ℕ} {S : Finset (Fin n)} {A : Op n} (h : IsLocal S A) :
    IsLocal S A.conjTranspose := by sorry

end
