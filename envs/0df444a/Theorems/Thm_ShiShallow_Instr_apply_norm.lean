-- Prove2me | Theorems.Thm_ShiShallow_Instr_apply_norm
-- name    : ShiShallow.Instr.apply_norm
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:46:11.045564+00:00
-- url     : https://prove2.me/theorems/d0e61fd3-f787-4548-b5de-3c3adc80db81
-- title:
--   Every gate preserves total squared modulus
-- statement:
--   Each instruction leaves the sum of ‖amplitude‖² over basis strings unchanged.
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
import Theorems.Thm_ShiShallow_hMat_unitary
import Theorems.Thm_ShiShallow_sMat_unitary
import Theorems.Thm_ShiShallow_sum_norm_sq_apply1
import Theorems.Thm_ShiShallow_sum_norm_sq_cnotState
import Theorems.Thm_ShiShallow_tMat_unitary

section
open ShiShallow

theorem ShiShallow.Instr.apply_norm {n : ℕ} (g : Instr n) (ψ : QState n) :
    ∑ x : Bits n, ‖g.apply ψ x‖ ^ 2 = ∑ x : Bits n, ‖ψ x‖ ^ 2 := by sorry

end
