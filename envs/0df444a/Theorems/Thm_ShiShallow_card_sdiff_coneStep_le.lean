-- Prove2me | Theorems.Thm_ShiShallow_card_sdiff_coneStep_le
-- name    : ShiShallow.card_sdiff_coneStep_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:29:36.164325+00:00
-- url     : https://prove2.me/theorems/44126b53-c9d3-4322-95b0-18b44fac909c
-- title:
--   New wires are bounded by the number of meeting gates
-- statement:
--   The wires added by one backward layer step are at most the number of gates in that layer whose support meets S.
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
import Theorems.Thm_ShiShallow_card_sdiff_support_le_one

section
open ShiShallow

theorem ShiShallow.card_sdiff_coneStep_le {n : ℕ} (l : List (Instr n)) (S : Finset (Fin n)) :
    ((coneStep l S) \ S).card
      ≤ (l.filter (fun g => decide (g.support ∩ S).Nonempty)).length := by sorry

end
