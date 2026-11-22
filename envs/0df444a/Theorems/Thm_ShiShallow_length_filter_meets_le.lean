-- Prove2me | Theorems.Thm_ShiShallow_length_filter_meets_le
-- name    : ShiShallow.length_filter_meets_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:54:43.10267+00:00
-- url     : https://prove2.me/theorems/fd1e1305-aaba-42e1-a39b-6247acc59e32
-- title:
--   Disjoint supports bound the number of meeting gates
-- statement:
--   In a layer whose gates act on pairwise disjoint wires, the number of gates whose support meets S is at most the cardinality of S.
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

section
open ShiShallow

theorem ShiShallow.length_filter_meets_le {n : ℕ} (l : List (Instr n)) (hl : LayerOk l) :
    ∀ S : Finset (Fin n),
      (l.filter (fun g => decide (g.support ∩ S).Nonempty)).length ≤ S.card := by sorry

end
