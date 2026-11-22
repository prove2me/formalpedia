-- Prove2me | Theorems.Thm_ShiShallow_sMat_unitary
-- name    : ShiShallow.sMat_unitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:56:31.918859+00:00
-- url     : https://prove2.me/theorems/7c9b4e57-557a-4795-a525-5a0d83153a8a
-- title:
--   The phase gate S is unitary
-- statement:
--   The 2x2 phase-gate matrix satisfies Sᴴ S = 1.
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

theorem ShiShallow.sMat_unitary : sMat.conjTranspose * sMat = 1 := by sorry

end
