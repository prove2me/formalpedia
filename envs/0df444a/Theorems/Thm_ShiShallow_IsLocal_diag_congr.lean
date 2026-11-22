-- Prove2me | Theorems.Thm_ShiShallow_IsLocal_diag_congr
-- name    : ShiShallow.IsLocal.diag_congr
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:20:00.526821+00:00
-- url     : https://prove2.me/theorems/b751c2c3-e414-49af-bfa3-de54f4257574
-- title:
--   Diagonal entries of a local operator depend only on its support
-- statement:
--   If A is S-local and two basis strings agree on S, the corresponding diagonal entries of A are equal. This is the step that converts cone-locality into the semantic cone theorem.
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

theorem ShiShallow.IsLocal.diag_congr {n : ℕ} {S : Finset (Fin n)} {A : Op n} (h : IsLocal S A)
    {x x' : Bits n} (hx : ∀ k ∈ S, x k = x' k) : A x x = A x' x' := by sorry

end
