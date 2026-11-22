-- Prove2me | Theorems.Thm_ShiShallow_ofReal_norm_sq
-- name    : ShiShallow.ofReal_norm_sq
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:26:47.482081+00:00
-- url     : https://prove2.me/theorems/be91a31a-731d-4483-a77b-f246fae84ad0
-- title:
--   Squared modulus as a conjugate product
-- statement:
--   For a complex number z, the real number ‖z‖² coerced to ℂ equals conj(z) * z.
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

theorem ShiShallow.ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by sorry

end
