-- Prove2me | Theorems.Thm_ShiShallow_isLocal_conj
-- name    : ShiShallow.isLocal_conj
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:46:47.171138+00:00
-- url     : https://prove2.me/theorems/3c9eb0b6-8d44-4a37-b771-88428ec4283c
-- title:
--   Conjugation grows the support by the gate's wires
-- statement:
--   Conjugating a T-local operator by a G-local operator yields a (G ∪ T)-local operator.
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
import Theorems.Thm_ShiShallow_IsLocal_mul

section
open ShiShallow

theorem ShiShallow.isLocal_conj {n : ℕ} {T G : Finset (Fin n)} {A V : Op n}
    (hA : IsLocal T A) (hV : IsLocal G V) :
    IsLocal (G ∪ T) (V.conjTranspose * A * V) := by sorry

end
