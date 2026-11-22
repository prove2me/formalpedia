-- Prove2me | Theorems.Thm_ShiShallow_sum_norm_sq_apply1
-- name    : ShiShallow.sum_norm_sq_apply1
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:29:58.042452+00:00
-- url     : https://prove2.me/theorems/5aa92fef-a95b-436a-8393-9bc447289cd0
-- title:
--   One-qubit gates preserve total squared modulus
-- statement:
--   Applying a unitary one-qubit gate to a wire leaves the sum of ‖amplitude‖² over all basis strings unchanged.
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
import Theorems.Thm_ShiShallow_apply1_at_fibre
import Theorems.Thm_ShiShallow_sum_norm_sq_mulVec

section
open ShiShallow

theorem ShiShallow.sum_norm_sq_apply1 {n : ℕ} {U : Matrix Bool Bool ℂ}
    (hU : U.conjTranspose * U = 1) (i : Fin n) (ψ : QState n) :
    ∑ x : Bits n, ‖apply1 U i ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by sorry

end
