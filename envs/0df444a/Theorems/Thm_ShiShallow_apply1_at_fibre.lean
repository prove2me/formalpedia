-- Prove2me | Theorems.Thm_ShiShallow_apply1_at_fibre
-- name    : ShiShallow.apply1_at_fibre
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:06:10.504763+00:00
-- url     : https://prove2.me/theorems/269c1497-b03c-430a-80fc-44ea6cdcc371
-- title:
--   One-qubit gate acts fibrewise
-- statement:
--   Evaluated on the fibre over wire i, a one-qubit gate acts as the 2x2 matrix on that wire's bit alone.
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
import Theorems.Thm_ShiShallow_funSplitAt_symm_at_i
import Theorems.Thm_ShiShallow_update_funSplitAt_symm

section
open ShiShallow

theorem ShiShallow.apply1_at_fibre {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n)
    (a : Bool) (r : {j : Fin n // j ≠ i} → Bool) :
    apply1 U i ψ ((Equiv.funSplitAt i Bool).symm (a, r))
      = ∑ b : Bool, U a b * ψ ((Equiv.funSplitAt i Bool).symm (b, r)) := by sorry

end
