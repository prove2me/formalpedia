-- Prove2me | Theorems.Thm_ShiShallow_inv_sqrt_two_mul_self
-- name    : ShiShallow.inv_sqrt_two_mul_self
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:17:43.856003+00:00
-- url     : https://prove2.me/theorems/8e9259fd-9961-4b59-9f0f-1b812e0d86ef
-- title:
--   One over root two, squared
-- statement:
--   The complex number (sqrt 2)⁻¹ multiplied by itself equals 1/2.
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

theorem ShiShallow.inv_sqrt_two_mul_self : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by sorry

end
