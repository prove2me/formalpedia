-- Prove2me | Theorems.Thm_ShiShallow_IsLocal_mono
-- name    : ShiShallow.IsLocal.mono
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:20:33.73385+00:00
-- url     : https://prove2.me/theorems/41daa660-7dfa-40bf-b89a-53262b86ba66
-- title:
--   Locality to a larger wire set is weaker
-- statement:
--   If A is S-local and S is contained in S', then A is S'-local.
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

theorem ShiShallow.IsLocal.mono {n : ℕ} {S S' : Finset (Fin n)} {A : Op n} (hSS : S ⊆ S')
    (h : IsLocal S A) : IsLocal S' A := by sorry

end
