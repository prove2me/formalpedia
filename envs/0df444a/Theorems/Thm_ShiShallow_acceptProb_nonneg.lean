-- Prove2me | Theorems.Thm_ShiShallow_acceptProb_nonneg
-- name    : ShiShallow.acceptProb_nonneg
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:18:48.197077+00:00
-- url     : https://prove2.me/theorems/155239cd-f87b-4e14-a80d-15651aaa477e
-- title:
--   Acceptance probability is nonnegative
-- statement:
--   acceptProb is at least 0.
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

theorem ShiShallow.acceptProb_nonneg {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) :
    0 ≤ acceptProb c x out := by sorry

end
