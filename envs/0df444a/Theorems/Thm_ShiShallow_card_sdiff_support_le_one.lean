-- Prove2me | Theorems.Thm_ShiShallow_card_sdiff_support_le_one
-- name    : ShiShallow.card_sdiff_support_le_one
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:05:01.026912+00:00
-- url     : https://prove2.me/theorems/503a9d56-f426-4408-a89f-e4e4b56c4586
-- title:
--   A meeting gate adds at most one new wire
-- statement:
--   If a gate's support meets S, then the support contributes at most one wire outside S, because the gate has fan-in at most two and already has a wire inside S.
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
import Theorems.Thm_ShiShallow_card_support_le_two

section
open ShiShallow

theorem ShiShallow.card_sdiff_support_le_one {n : ℕ} (g : Instr n) (S : Finset (Fin n))
    (h : (g.support ∩ S).Nonempty) : (g.support \ S).card ≤ 1 := by sorry

end
