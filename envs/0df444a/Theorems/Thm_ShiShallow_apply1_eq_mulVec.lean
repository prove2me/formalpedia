-- Prove2me | Theorems.Thm_ShiShallow_apply1_eq_mulVec
-- name    : ShiShallow.apply1_eq_mulVec
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:21:51.195908+00:00
-- url     : https://prove2.me/theorems/73fcce61-d79b-4561-8b2d-04570755e501
-- title:
--   One-qubit gate semantics is matrix-vector multiplication
-- statement:
--   Applying a one-qubit gate U to wire i of a state equals multiplying the state by the embedded matrix of U.
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

theorem ShiShallow.apply1_eq_mulVec {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n) :
    apply1 U i ψ = (apply1Matrix U i).mulVec ψ := by sorry

end
