-- Prove2me | Theorems.Thm_ShiShallow_sum_norm_sq_cnotState
-- name    : ShiShallow.sum_norm_sq_cnotState
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:55:11.84296+00:00
-- url     : https://prove2.me/theorems/c0572b7f-6a38-4f41-908f-15218c1b34aa
-- title:
--   CNOT preserves total squared modulus
-- statement:
--   CNOT permutes basis strings, so it leaves the sum of ‖amplitude‖² unchanged.
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

theorem ShiShallow.sum_norm_sq_cnotState {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    ∑ x : Bits n, ‖cnotState i j hij ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by sorry

end
