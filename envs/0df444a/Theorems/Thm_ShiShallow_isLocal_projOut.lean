-- Prove2me | Theorems.Thm_ShiShallow_isLocal_projOut
-- name    : ShiShallow.isLocal_projOut
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:26:29.460372+00:00
-- url     : https://prove2.me/theorems/fda2756f-f159-4afd-b302-9360e2706119
-- title:
--   The measurement projector is local to the measured wire
-- statement:
--   The projector onto 'output wire reads 1' is {out}-local.
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

theorem ShiShallow.isLocal_projOut {n : ℕ} (out : Fin n) : IsLocal {out} (projOut out) := by sorry

end
