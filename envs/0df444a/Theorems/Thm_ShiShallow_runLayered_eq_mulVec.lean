-- Prove2me | Theorems.Thm_ShiShallow_runLayered_eq_mulVec
-- name    : ShiShallow.runLayered_eq_mulVec
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:47:16.610024+00:00
-- url     : https://prove2.me/theorems/8f73dfba-8a2a-4159-82ab-968117d651e9
-- title:
--   Circuit semantics is matrix-vector multiplication
-- statement:
--   Running a layered circuit on a state equals multiplying by the circuit matrix.
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
import Theorems.Thm_ShiShallow_runLayer_eq_mulVec

section
open ShiShallow

theorem ShiShallow.runLayered_eq_mulVec {n : ℕ} (c : Layered n) (ψ : QState n) :
    runLayered c ψ = (circMatrix c).mulVec ψ := by sorry

end
