-- Prove2me | Theorems.Thm_ShiShallow_apply1Matrix_unitary
-- name    : ShiShallow.apply1Matrix_unitary
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:08:42.722457+00:00
-- url     : https://prove2.me/theorems/61946e50-573a-42fb-80e1-60f782b6cb2d
-- title:
--   Embedding a unitary on one wire stays unitary
-- statement:
--   If U is a unitary 2x2 matrix, the operator that applies U to wire i and the identity elsewhere is unitary on the full 2ⁿ-dimensional space.
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
import Theorems.Thm_ShiShallow_isLocal_apply1Matrix
import Theorems.Thm_ShiShallow_sum_of_vanishing_single

section
open ShiShallow

theorem ShiShallow.apply1Matrix_unitary {n : ℕ} {U : Matrix Bool Bool ℂ} (hU : U.conjTranspose * U = 1) (i : Fin n) :
    (apply1Matrix U i).conjTranspose * apply1Matrix U i = 1 := by sorry

end
