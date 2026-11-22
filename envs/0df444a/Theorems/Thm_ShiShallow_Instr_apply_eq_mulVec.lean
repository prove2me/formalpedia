-- Prove2me | Theorems.Thm_ShiShallow_Instr_apply_eq_mulVec
-- name    : ShiShallow.Instr.apply_eq_mulVec
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:07:39.266523+00:00
-- url     : https://prove2.me/theorems/f72aaf39-01d2-478b-8f5c-d75a12fc14f1
-- title:
--   Gate semantics is matrix-vector multiplication
-- statement:
--   For every instruction, the state-level action agrees with multiplication by the instruction's matrix.
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
import Theorems.Thm_ShiShallow_apply1_eq_mulVec
import Theorems.Thm_ShiShallow_cnotState_eq_mulVec

section
open ShiShallow

theorem ShiShallow.Instr.apply_eq_mulVec {n : ℕ} (g : Instr n) (ψ : QState n) :
    g.apply ψ = (gateMatrix g).mulVec ψ := by sorry

end
