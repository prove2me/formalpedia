-- Prove2me | Theorems.Thm_ShiShallow_runLayer_eq_mulVec
-- name    : ShiShallow.runLayer_eq_mulVec
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:31:48.085809+00:00
-- url     : https://prove2.me/theorems/c065bbff-a629-4664-afde-bfea38dd425e
-- title:
--   Layer semantics is matrix-vector multiplication
-- statement:
--   Running a layer on a state equals multiplying by the layer's matrix (the product of its gate matrices, in reverse application order).
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
import Theorems.Thm_ShiShallow_Instr_apply_eq_mulVec

section
open ShiShallow

theorem ShiShallow.runLayer_eq_mulVec {n : ℕ} (l : List (Instr n)) (ψ : QState n) :
    runLayer l ψ = (layerMatrix l).mulVec ψ := by sorry

end
