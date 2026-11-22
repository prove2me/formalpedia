-- Prove2me | Theorems.Thm_ShiShallow_support_nonempty
-- name    : ShiShallow.support_nonempty
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:53:50.687125+00:00
-- url     : https://prove2.me/theorems/eaf45244-d240-4ada-903c-08413ba81bfe
-- title:
--   Every gate acts on at least one wire
-- statement:
--   The support of any instruction (H, S, T or CNOT) is a nonempty finite set of wires.
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

theorem ShiShallow.support_nonempty {n : ℕ} (g : Instr n) : g.support.Nonempty := by sorry

end
