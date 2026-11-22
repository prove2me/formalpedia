-- Prove2me | Theorems.Thm_ShiShallow_acceptProb_append_x
-- name    : ShiShallow.acceptProb_append_x
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:03:48.793131+00:00
-- url     : https://prove2.me/theorems/5b1962d5-0b68-4ea8-aa95-cf23185c5699
-- title:
--   Appending a bit flip complements the acceptance probability
-- statement:
--   Let $c$ be a circuit with designated output wire $\mathrm{out}$, and let $c'$ be $c$ followed by one further layer consisting of a single bit flip $X$ on that wire. Then
--
--   $$\Pr[c' \text{ accepts } x] \;=\; 1 - \Pr[c \text{ accepts } x].$$
--
--   The proof is a change of variables: $X$ on wire $\mathrm{out}$ permutes basis strings by the involution that flips the bit at $\mathrm{out}$, so the acceptance sum for $c'$ is the rejection sum for $c$; the two sum to the total mass, which is $1$ by norm preservation.
--
--   This is the circuit-level content of closure under complement: negating the answer costs exactly one extra layer and changes neither the gate set nor the error.
-- source:
--   Formalised from scratch in this development; the light-cone bound is the standard shallow-circuit argument, see e.g. Terhal--DiVincenzo, Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games, arXiv:quant-ph/0205133.

import Definitions.Def_ShiShallow_Core

namespace ShiShallow
theorem acceptProb_append_x {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) :
    acceptProb (c ++ [[Instr.x out]]) x out = 1 - acceptProb c x out := by sorry
end ShiShallow
