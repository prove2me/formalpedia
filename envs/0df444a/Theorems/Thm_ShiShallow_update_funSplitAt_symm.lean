-- Prove2me | Theorems.Thm_ShiShallow_update_funSplitAt_symm
-- name    : ShiShallow.update_funSplitAt_symm
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:17:27.486716+00:00
-- url     : https://prove2.me/theorems/9913bce9-9439-4466-a601-974d1d08cec1
-- title:
--   Updating a wire commutes with the fibre splitting
-- statement:
--   Overwriting wire i of a reassembled bit-string is the same as reassembling with the new bit at i.
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

theorem ShiShallow.update_funSplitAt_symm {n : ℕ} (i : Fin n) (a b : Bool)
    (r : {j : Fin n // j ≠ i} → Bool) :
    Function.update ((Equiv.funSplitAt i Bool).symm (a, r)) i b
      = (Equiv.funSplitAt i Bool).symm (b, r) := by sorry

end
