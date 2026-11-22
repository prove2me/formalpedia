-- Prove2me | Theorems.Thm_ShiShallow_mul_comm_of_disjoint
-- name    : ShiShallow.mul_comm_of_disjoint
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:24:28.422141+00:00
-- url     : https://prove2.me/theorems/a76a36e3-8892-44a2-8402-73691f38c272
-- title:
--   Disjointly supported operators commute
-- statement:
--   If A acts only on T and V only on G, with G and T disjoint, then AV = VA.
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

theorem ShiShallow.mul_comm_of_disjoint {n : ℕ} {G T : Finset (Fin n)} {A V : Op n}
    (hA : IsLocal T A) (hV : IsLocal G V) (hd : Disjoint G T) : A * V = V * A := by sorry

end
