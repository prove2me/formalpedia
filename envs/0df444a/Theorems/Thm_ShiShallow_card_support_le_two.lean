-- Prove2me | Theorems.Thm_ShiShallow_card_support_le_two
-- name    : ShiShallow.card_support_le_two
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:54:17.225301+00:00
-- url     : https://prove2.me/theorems/8e6dff27-3c20-4720-b1c1-f03e1f8efd03
-- title:
--   Gates have fan-in at most two
-- statement:
--   Every instruction acts on at most two wires: one-qubit gates on one, CNOT on two.
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

section
open ShiShallow

theorem ShiShallow.card_support_le_two {n : ℕ} (g : Instr n) : g.support.card ≤ 2 := by sorry

end
