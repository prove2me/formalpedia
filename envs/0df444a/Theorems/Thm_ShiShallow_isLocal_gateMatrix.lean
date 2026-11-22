-- Prove2me | Theorems.Thm_ShiShallow_isLocal_gateMatrix
-- name    : ShiShallow.isLocal_gateMatrix
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:08:13.366987+00:00
-- url     : https://prove2.me/theorems/2b20af21-10d7-411a-9cc6-6802c03e2f9a
-- title:
--   Every gate matrix is local to the gate's support
-- statement:
--   Each instruction's matrix is local to exactly the wires the instruction acts on.
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
import Theorems.Thm_ShiShallow_isLocal_apply1Matrix
import Theorems.Thm_ShiShallow_isLocal_cnotMatrix

section
open ShiShallow

theorem ShiShallow.isLocal_gateMatrix {n : ℕ} (g : Instr n) : IsLocal g.support (gateMatrix g) := by sorry

end
