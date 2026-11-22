-- Prove2me | Theorems.Thm_ShiShallow_conj_mul_eq
-- name    : ShiShallow.conj_mul_eq
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:10:19.55465+00:00
-- url     : https://prove2.me/theorems/2bf4a474-5762-4d63-8068-e826eb25590d
-- title:
--   Conjugation by a product factorises
-- statement:
--   (XY)ᴴ A (XY) = Yᴴ (Xᴴ A X) Y: conjugating by a product is conjugating by each factor in turn.
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
import Theorems.Thm_ShiShallow_IsLocal_conjTranspose

section
open ShiShallow

theorem ShiShallow.conj_mul_eq {n : ℕ} (A X Y : Op n) :
    (X * Y).conjTranspose * A * (X * Y)
      = Y.conjTranspose * (X.conjTranspose * A * X) * Y := by sorry

end
