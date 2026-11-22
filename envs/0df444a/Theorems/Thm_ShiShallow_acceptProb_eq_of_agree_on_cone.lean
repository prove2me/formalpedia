-- Prove2me | Theorems.Thm_ShiShallow_acceptProb_eq_of_agree_on_cone
-- name    : ShiShallow.acceptProb_eq_of_agree_on_cone
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T06:02:40.366909+00:00
-- url     : https://prove2.me/theorems/3469a157-1a45-4847-a6a5-8ffc3191b6be
-- title:
--   Semantic causal cone theorem
-- statement:
--   If two inputs agree on the causal cone of the output wire, the circuit accepts them with the same probability. The pairwise-disjoint-support hypothesis is essential: without it the statement is false, refuted by the single layer [cnot 2 1, cnot 1 0] on three wires.
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
import Definitions.Def_ShiShallow_Operator
import Theorems.Thm_ShiShallow_IsLocal_diag_congr
import Theorems.Thm_ShiShallow_acceptProb_eq_conj_entry
import Theorems.Thm_ShiShallow_isLocal_conj_circuit
import Theorems.Thm_ShiShallow_isLocal_projOut
import Theorems.Thm_ShiShallow_padIn_castAdd
import Theorems.Thm_ShiShallow_padIn_natAdd

section
open ShiShallow

theorem ShiShallow.acceptProb_eq_of_agree_on_cone {n m : ℕ} (c : Layered (n + m)) (out : Fin (n + m))
    (hc : ∀ l ∈ c, LayerOk l) (x x' : Bits n)
    (hagree : ∀ i : Fin n, Fin.castAdd m i ∈ coneOf c {out} → x i = x' i) :
    acceptProb c x out = acceptProb c x' out := by sorry

end
