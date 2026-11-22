-- Prove2me | Theorems.Thm_ShiShallow_cnotState_eq_mulVec
-- name    : ShiShallow.cnotState_eq_mulVec
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:22:27.167005+00:00
-- url     : https://prove2.me/theorems/3a79c1a7-75f6-44ce-b6f3-2fcce9c1bf4f
-- title:
--   CNOT semantics is matrix-vector multiplication
-- statement:
--   Applying CNOT with control i and target j to a state equals multiplying the state by the CNOT matrix.
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

theorem ShiShallow.cnotState_eq_mulVec {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    cnotState i j hij ψ = (cnotMatrix i j).mulVec ψ := by sorry

end
