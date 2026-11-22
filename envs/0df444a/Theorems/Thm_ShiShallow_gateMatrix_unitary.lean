-- Prove2me | Theorems.Thm_ShiShallow_gateMatrix_unitary
-- name    : ShiShallow.gateMatrix_unitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:30:36.686597+00:00
-- url     : https://prove2.me/theorems/8595d1fe-0c12-44b1-accd-1b31428adbcd
-- title:
--   Every gate matrix is unitary
-- statement:
--   Each instruction's 2ⁿ-dimensional matrix (H, S, T on a wire, or CNOT on two) satisfies Gᴴ G = 1.
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
import Definitions.Def_ShiShallow_Operator
import Theorems.Thm_ShiShallow_apply1Matrix_unitary
import Theorems.Thm_ShiShallow_cnotMatrix_unitary
import Theorems.Thm_ShiShallow_hMat_unitary
import Theorems.Thm_ShiShallow_sMat_unitary
import Theorems.Thm_ShiShallow_tMat_unitary

section
open ShiShallow

theorem ShiShallow.gateMatrix_unitary {n : ℕ} (g : Instr n) : (gateMatrix g).conjTranspose * gateMatrix g = 1 := by sorry

end
