-- Prove2me | Theorems.Thm_ShiShallow_conj_eq_of_disjoint
-- name    : ShiShallow.conj_eq_of_disjoint
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:09:43.99112+00:00
-- url     : https://prove2.me/theorems/e544c1bc-c10d-4750-b322-6515a2462e20
-- title:
--   A unitary missing the support cancels under conjugation
-- statement:
--   If V is unitary and supported on wires disjoint from the support of A, then Vᴴ A V = A. This cancellation is why a gate outside the cone leaves the observable untouched.
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
import Theorems.Thm_ShiShallow_mul_comm_of_disjoint

section
open ShiShallow

theorem ShiShallow.conj_eq_of_disjoint {n : ℕ} {G T : Finset (Fin n)} {A V : Op n}
    (hA : IsLocal T A) (hV : IsLocal G V) (hd : Disjoint G T)
    (hVu : V.conjTranspose * V = 1) : V.conjTranspose * A * V = A := by sorry

end
