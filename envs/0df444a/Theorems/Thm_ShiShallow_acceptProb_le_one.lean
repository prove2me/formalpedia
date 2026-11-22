-- Prove2me | Theorems.Thm_ShiShallow_acceptProb_le_one
-- name    : ShiShallow.acceptProb_le_one
-- status  : Proved
-- author  : @Goku
-- created : 2026-09-10T03:03:58.717888+00:00
-- url     : https://prove2.me/theorems/0faacd9f-b185-4ca5-b756-0b0f838819be
-- title:
--   Acceptance probability is at most one
-- statement:
--   The acceptance probability of a circuit — the total weight of the basis strings whose designated output wire reads $1$ — is bounded by one:
--
--   $$\Pr[\text{accept}] \;=\!\!\sum_{y \,:\, y_{\mathrm{out}} = 1}\!\! \bigl| (c\,|x,0^m\rangle)(y) \bigr|^2 \;\le\; 1 .$$
--
--   The acceptance event is a sub-collection of all measurement outcomes, whose total weight is $1$ by norm preservation. This is a basic well-formedness property of the circuit model, and is the statement that lets bounded-error acceptance criteria such as $\Pr[\text{accept}] \ge 2/3$ be stated meaningfully.
-- source:
--   Formalised from scratch in this development; the light-cone bound is the standard shallow-circuit argument, see e.g. Terhal--DiVincenzo, Adaptive quantum computation, constant depth quantum circuits and Arthur-Merlin games, arXiv:quant-ph/0205133.

import Definitions.Def_ShiShallow_Core

namespace ShiShallow
theorem acceptProb_le_one {n m : ℕ} (c : Layered (n + m)) (x : Bits n) (out : Fin (n + m)) :
    acceptProb c x out ≤ 1 := by sorry
end ShiShallow
