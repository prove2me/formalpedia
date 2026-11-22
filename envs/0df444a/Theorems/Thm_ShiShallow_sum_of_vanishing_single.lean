-- Prove2me | Theorems.Thm_ShiShallow_sum_of_vanishing_single
-- name    : ShiShallow.sum_of_vanishing_single
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:22:56.495188+00:00
-- url     : https://prove2.me/theorems/bdf41994-cb37-4971-890a-4d66c6b2cb86
-- title:
--   Collapse a sum to a single wire
-- statement:
--   The single-wire case of the fibre collapse: the sum reduces to a sum over the two values of that wire.
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

theorem ShiShallow.sum_of_vanishing_single {n : ℕ} (i : Fin n) (y : Bits n) (G : Bits n → ℂ)
    (hG : ∀ w : Bits n, (¬ ∀ k, k ∉ ({i} : Finset (Fin n)) → w k = y k) → G w = 0) :
    ∑ w : Bits n, G w = ∑ b : Bool, G (Function.update y i b) := by sorry

end
