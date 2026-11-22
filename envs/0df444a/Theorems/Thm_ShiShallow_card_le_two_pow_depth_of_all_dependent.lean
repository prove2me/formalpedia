-- Prove2me | Theorems.Thm_ShiShallow_card_le_two_pow_depth_of_all_dependent
-- name    : ShiShallow.card_le_two_pow_depth_of_all_dependent
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T06:14:11.152423+00:00
-- url     : https://prove2.me/theorems/47b8f0dd-47d4-42e4-8021-d33ce83bc3a5
-- title:
--   Depth lower bound from genuine functional dependence
-- statement:
--   Let $c$ be a quantum circuit of depth $d$ acting on $n$ input wires together with $m$ ancilla wires, built from gates of fan-in at most two and arranged in layers whose gates act on pairwise disjoint wires, and fix a designated output wire. For a classical input $x \in \{0,1\}^n$, let
--   $$p_c(x) \;=\; \Pr[\text{the output wire is measured } 1]$$
--   be the acceptance probability of the circuit run on $x$ with all ancillas initialised to $0$.
--   Say that the input wire $i$ **matters** if the acceptance probability genuinely depends on it, that is, if there are inputs $x, x'$ agreeing in every coordinate except $i$ with $p_c(x) \neq p_c(x')$. If every input wire matters, then
--   $$n \;\le\; 2^{\,d}.$$
--   This is the semantically honest form of the light-cone depth bound. The published syntactic version assumes instead that every input wire lies in the causal cone of the output; the cone only over-approximates the wires a value can depend on, so that hypothesis is weaker than genuine dependence and the bound above is correspondingly stronger. The restriction to layers of pairwise disjoint gates is essential rather than cosmetic: on three wires, the single layer consisting of $\mathrm{CNOT}_{2 \to 1}$ and $\mathrm{CNOT}_{1 \to 0}$ leaves wire $0$ holding $x_0 \oplus x_1 \oplus x_2$, so all three input wires matter at depth $1$, and $3 > 2^1$.
--
--   **Formalization Note.** Layer well-formedness is the hypothesis `LayerOk`, and the acceptance probability is `acceptProb`, the total squared-modulus weight of the basis strings whose output wire reads $1$; inputs are padded with zero ancillas via `inputState`.
-- source:
--   Original work by Yueheng Shi (Apache-2.0). Open problem posed as milestone 1 of the shallow-circuits mission.

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi

Shallow quantum circuits and causal cones.

MODIFICATIONS made for publication on Prove2me: the enclosing `namespace` is replaced by `section`+`open`; this statement is published OPEN (proof intentionally omitted).

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiShallow_Circuit

section
open ShiShallow

theorem ShiShallow.card_le_two_pow_depth_of_all_dependent {n m : ℕ}
    (c : Layered (n + m)) (out : Fin (n + m)) (hc : ∀ l ∈ c, LayerOk l)
    (hdep : ∀ i : Fin n, ∃ x x' : Bits n,
      (∀ j : Fin n, j ≠ i → x j = x' j) ∧ acceptProb c x out ≠ acceptProb c x' out) :
    n ≤ 2 ^ depth c := by sorry

end
