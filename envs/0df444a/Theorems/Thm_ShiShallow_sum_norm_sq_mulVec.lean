-- Prove2me | Theorems.Thm_ShiShallow_sum_norm_sq_mulVec
-- name    : ShiShallow.sum_norm_sq_mulVec
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:05:39.021843+00:00
-- url     : https://prove2.me/theorems/e95c0b62-32a5-479b-a458-007851084852
-- title:
--   Unitary matrices preserve the sum of squared moduli on one qubit
-- statement:
--   For a unitary 2x2 matrix U, the sum of ‖(Uv)_a‖² over a equals the sum of ‖v_b‖² over b.
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
import Mathlib
import Theorems.Thm_ShiShallow_sum_conj_mul_mulVec

section
open ShiShallow

theorem ShiShallow.sum_norm_sq_mulVec {U : Matrix Bool Bool ℂ} (hU : U.conjTranspose * U = 1)
    (v : Bool → ℂ) :
    ∑ a : Bool, ‖∑ b : Bool, U a b * v b‖ ^ 2 = ∑ b : Bool, ‖v b‖ ^ 2 := by sorry

end
