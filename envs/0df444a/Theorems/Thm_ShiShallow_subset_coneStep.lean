-- Prove2me | Theorems.Thm_ShiShallow_subset_coneStep
-- name    : ShiShallow.subset_coneStep
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:53:28.750401+00:00
-- url     : https://prove2.me/theorems/6664c445-fab0-4efa-bb51-e400679e2d3c
-- title:
--   Causal cone contains its seed (one layer)
-- statement:
--   Propagating a set of wires back through a single layer can only enlarge it: S is a subset of coneStep l S.
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
import Definitions.Def_ShiShallow_Cone

section
open ShiShallow

theorem ShiShallow.subset_coneStep {n : ℕ} (l : List (Instr n)) (S : Finset (Fin n)) :
    S ⊆ coneStep l S := by sorry

end
