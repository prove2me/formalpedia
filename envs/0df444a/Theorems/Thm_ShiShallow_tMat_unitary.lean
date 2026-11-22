-- Prove2me | Theorems.Thm_ShiShallow_tMat_unitary
-- name    : ShiShallow.tMat_unitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:57:17.547599+00:00
-- url     : https://prove2.me/theorems/41942978-5c2d-4b65-a729-b27e88400380
-- title:
--   The T gate is unitary
-- statement:
--   The 2x2 T-gate matrix satisfies Tᴴ T = 1.
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

theorem ShiShallow.tMat_unitary : tMat.conjTranspose * tMat = 1 := by sorry

end
