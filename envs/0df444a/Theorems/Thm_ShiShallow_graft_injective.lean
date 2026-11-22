-- Prove2me | Theorems.Thm_ShiShallow_graft_injective
-- name    : ShiShallow.graft_injective
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:19:30.104218+00:00
-- url     : https://prove2.me/theorems/e8147b5a-99fd-467a-864a-551cdc710c4e
-- title:
--   Grafting is injective
-- statement:
--   Overwriting a fixed bit-string on a wire set S is injective in the overwritten values.
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

theorem ShiShallow.graft_injective {n : ℕ} (S : Finset (Fin n)) (v : Bits n) :
    Function.Injective (graft S v) := by sorry

end
