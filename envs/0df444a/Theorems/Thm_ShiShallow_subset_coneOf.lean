-- Prove2me | Theorems.Thm_ShiShallow_subset_coneOf
-- name    : ShiShallow.subset_coneOf
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:04:35.876242+00:00
-- url     : https://prove2.me/theorems/67387ff8-df77-4e52-98c2-ec4a006a47d9
-- title:
--   Causal cone contains its seed
-- statement:
--   Propagating a set of wires back through a whole layered circuit can only enlarge it: S is a subset of coneOf c S.
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
import Theorems.Thm_ShiShallow_subset_coneStep

section
open ShiShallow

theorem ShiShallow.subset_coneOf {n : ℕ} (c : Layered n) (S : Finset (Fin n)) : S ⊆ coneOf c S := by sorry

end
