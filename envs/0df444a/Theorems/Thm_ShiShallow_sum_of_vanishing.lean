-- Prove2me | Theorems.Thm_ShiShallow_sum_of_vanishing
-- name    : ShiShallow.sum_of_vanishing
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:07:16.58789+00:00
-- url     : https://prove2.me/theorems/dda31361-a4dd-424d-ab52-12fd417f1c10
-- title:
--   Collapse a sum to a gate's own wires
-- statement:
--   A sum over all basis strings whose summand vanishes off the fibre {u : u agrees with v outside S} collapses to a sum over the values on S alone.
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
import Theorems.Thm_ShiShallow_graft_injective

section
open ShiShallow

theorem ShiShallow.sum_of_vanishing {n : ℕ} (S : Finset (Fin n)) (v : Bits n) (F : Bits n → ℂ)
    (hF : ∀ u : Bits n, (¬ ∀ k, k ∉ S → u k = v k) → F u = 0) :
    ∑ u : Bits n, F u = ∑ w : {k : Fin n // k ∈ S} → Bool, F (graft S v w) := by sorry

end
