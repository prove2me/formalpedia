-- Prove2me | Theorems.Thm_ShiShallow_sum_conj_mul_mulVec
-- name    : ShiShallow.sum_conj_mul_mulVec
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:16:50.143904+00:00
-- url     : https://prove2.me/theorems/7f87b288-3d2d-494b-8ab6-1a3b9eed3f16
-- title:
--   Unitary invariance of the conjugate form on one qubit
-- statement:
--   For a unitary 2x2 matrix U, the sum over outputs of conj((Uv)_a) (Uv)_a equals the same sum for v.
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

section

theorem ShiShallow.sum_conj_mul_mulVec {U : Matrix Bool Bool ℂ} (hU : U.conjTranspose * U = 1)
    (v : Bool → ℂ) :
    ∑ a : Bool, (starRingEnd ℂ) (∑ b : Bool, U a b * v b) * (∑ b : Bool, U a b * v b)
      = ∑ b : Bool, (starRingEnd ℂ) (v b) * v b := by sorry

end
