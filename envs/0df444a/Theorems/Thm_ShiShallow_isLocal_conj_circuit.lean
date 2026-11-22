-- Prove2me | Theorems.Thm_ShiShallow_isLocal_conj_circuit
-- name    : ShiShallow.isLocal_conj_circuit
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T05:59:31.203417+00:00
-- url     : https://prove2.me/theorems/fd1ba8a9-9857-461f-a192-a0659faa3909
-- title:
--   The conjugated observable lives inside the causal cone
-- statement:
--   Let $c$ be a layered circuit whose gates within each layer act on pairwise disjoint wires, and let $U_c$ denote the unitary it implements. Call an operator $A$ **local to** a set $S$ of wires when it acts as the identity off $S$, that is, $A = A_S \otimes I$. If $A$ is local to $S$, then its backward conjugate by the circuit is local to the causal cone of $S$:
--   $$U_c^{\dagger} A\, U_c \ \text{ is local to } \ \mathrm{cone}_c(S).$$
--   This is the Heisenberg-picture form of the light-cone principle, and it is what converts a syntactic statement about which wires a circuit mentions into a statement about what the circuit computes: a gate whose wires miss the observable's support commutes with it and cancels against its own adjoint, so only gates inside the cone can enlarge the support. Pairwise disjointness within a layer is required: on three wires, conjugating the projector onto wire $0$ through the single layer $\mathrm{CNOT}_{2 \to 1}, \mathrm{CNOT}_{1 \to 0}$ yields the observable measuring $x_0 \oplus x_1 \oplus x_2$, which is not local to $\{0,1\}$, the cone of $\{0\}$.
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
import Theorems.Thm_ShiShallow_IsLocal_conjTranspose
import Theorems.Thm_ShiShallow_conj_mul_eq
import Theorems.Thm_ShiShallow_isLocal_conj_layer

section
open ShiShallow

theorem ShiShallow.isLocal_conj_circuit {n : ℕ} (c : Layered n) (hc : ∀ l ∈ c, LayerOk l)
    {S : Finset (Fin n)} {A : Op n} (hA : IsLocal S A) :
    IsLocal (coneOf c S) ((circMatrix c).conjTranspose * A * circMatrix c) := by sorry

end
