-- Prove2me | Theorems.Thm_ShiShallow_isLocal_apply1Matrix
-- name    : ShiShallow.isLocal_apply1Matrix
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:20:58.82279+00:00
-- url     : https://prove2.me/theorems/d9aed559-4031-4043-a12a-2184e1a093f0
-- title:
--   One-qubit gate matrices are local to their wire
-- statement:
--   The embedded matrix of a one-qubit gate on wire i is {i}-local: entries vanish unless the two basis strings agree off i, and depend only on the bits at i.
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

section
open ShiShallow

theorem ShiShallow.isLocal_apply1Matrix {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) :
    IsLocal {i} (apply1Matrix U i) := by sorry

end
