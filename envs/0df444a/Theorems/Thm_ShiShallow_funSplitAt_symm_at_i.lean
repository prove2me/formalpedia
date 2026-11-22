-- Prove2me | Theorems.Thm_ShiShallow_funSplitAt_symm_at_i
-- name    : ShiShallow.funSplitAt_symm_at_i
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:17:11.172466+00:00
-- url     : https://prove2.me/theorems/359bd400-3f7f-48ab-ac13-d31b7a1d058b
-- title:
--   Splitting a bit-string at a wire recovers that wire's bit
-- statement:
--   Reassembling a bit-string from its value at wire i and its values elsewhere gives back the original bit at i.
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

theorem ShiShallow.funSplitAt_symm_at_i {n : ℕ} (i : Fin n) (a : Bool)
    (r : {j : Fin n // j ≠ i} → Bool) :
    (Equiv.funSplitAt i Bool).symm (a, r) i = a := by sorry

end
