-- Prove2me | Theorems.Thm_ShiShallow_runLayer_norm
-- name    : ShiShallow.runLayer_norm
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:52:37.93099+00:00
-- url     : https://prove2.me/theorems/bbf288e2-114f-478b-8738-5ac619eccb72
-- title:
--   Layers preserve total squared modulus
-- statement:
--   Running a layer leaves the sum of ‖amplitude‖² unchanged.
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
import Theorems.Thm_ShiShallow_Instr_apply_norm

section
open ShiShallow

theorem ShiShallow.runLayer_norm {n : ℕ} (l : List (Instr n)) (ψ : QState n) :
    ∑ x : Bits n, ‖runLayer l ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by sorry

end
