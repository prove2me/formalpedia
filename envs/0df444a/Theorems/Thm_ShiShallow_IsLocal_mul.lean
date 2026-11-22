-- Prove2me | Theorems.Thm_ShiShallow_IsLocal_mul
-- name    : ShiShallow.IsLocal.mul
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:31:05.479331+00:00
-- url     : https://prove2.me/theorems/950a6d74-4430-4f5d-b475-9e8d135e0bec
-- title:
--   Products of local operators are local to the union
-- statement:
--   If X is S₁-local and Y is S₂-local then XY is (S₁ ∪ S₂)-local.
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
import Theorems.Thm_ShiShallow_sum_of_vanishing

section
open ShiShallow

theorem ShiShallow.IsLocal.mul {n : ℕ} {S₁ S₂ : Finset (Fin n)} {X Y : Op n}
    (hX : IsLocal S₁ X) (hY : IsLocal S₂ Y) : IsLocal (S₁ ∪ S₂) (X * Y) := by sorry

end
