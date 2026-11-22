-- Prove2me | Theorems.Thm_ShiShallow_disjoint_coneStep
-- name    : ShiShallow.disjoint_coneStep
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T04:24:55.981463+00:00
-- url     : https://prove2.me/theorems/2751eaa1-258f-47d1-ab8f-ef0ad64d8383
-- title:
--   Cone steps preserve disjointness
-- statement:
--   If a set of wires G is disjoint from S and from the support of every gate in a layer, then G is disjoint from the backward cone step of S through that layer.
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

theorem ShiShallow.disjoint_coneStep {n : ℕ} {G : Finset (Fin n)} (l : List (Instr n)) (S : Finset (Fin n))
    (hS : Disjoint G S) (ht : ∀ g ∈ l, Disjoint G g.support) : Disjoint G (coneStep l S) := by sorry

end
