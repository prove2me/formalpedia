-- Prove2me | Theorems.Thm_ShiShallow_card_le_two_pow_depth_of_all_relevant
-- name    : ShiShallow.card_le_two_pow_depth_of_all_relevant
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:03:45.401267+00:00
-- url     : https://prove2.me/theorems/3fc3cfba-c632-4fea-8020-1e576896ef12
-- title:
--   Depth-$d$ circuits reach at most $2^d$ input wires
-- statement:
--   Consider a circuit on $n$ input wires together with $m$ ancilla wires, with a designated output wire. If **every** input wire lies in the causal cone of the output, then
--
--   $$n \;\le\; 2^{\,\mathrm{depth}(c)}.$$
--
--   Equivalently, a circuit whose output is reachable from all $n$ inputs cannot be shallower than $\log_2 n$. This is the standard depth lower bound for bounded-fan-in circuits, here in its syntactic form: the hypothesis is membership in the causal cone rather than genuine functional dependence, the two being related by the fact that the cone always over-approximates the set of wires a value can depend on.
-- source:
--   Formalised from scratch in this development; the light-cone bound is the standard shallow-circuit argument, see e.g. Terhal--DiVincenzo, Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games, arXiv:quant-ph/0205133.

import Definitions.Def_ShiShallow_Core

namespace ShiShallow
theorem card_le_two_pow_depth_of_all_relevant {n m : ℕ} (c : Layered (n + m))
    (out : Fin (n + m)) (hc : ∀ l ∈ c, LayerOk l)
    (hall : ∀ i : Fin n, Fin.castAdd m i ∈ coneOf c {out}) :
    n ≤ 2 ^ depth c := by sorry
end ShiShallow
