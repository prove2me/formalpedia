-- Prove2me | Theorems.Thm_SteinbergFalse_Counterexample_G_noFourFiveCycle
-- name    : SteinbergFalse.Counterexample.G_noFourFiveCycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:28.211987+00:00
-- url     : https://prove2.me/theorems/930b1024-e568-4786-8e86-9884c0b21d99
-- title:
--   Proof of Theorem 3 — the graph $G$ of Figure 3 has no cycle of length four or five
-- statement:
--   Let $G$ be the 166-vertex graph of Figure 3, built from four copies of $G_2$ and twelve further edges. Then $G$ has no cycle of length four or five:
--
--   $$
--   \text{every cycle } C \text{ of } G \text{ satisfies } |C| \notin \{4, 5\}.
--   $$
--
--   This is the first of the two properties of $G$ established in the proof of Theorem 3; together with the non-3-colorability of $G$ and its planarity it shows that $G$ is a counterexample to Steinberg's Conjecture.
--
--   **Formalization Note** Cycles are Mathlib walks with `Walk.IsCycle`, as in the definition `NoFourFiveCycle`.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, pp. 4–5, proof of Theorem 3 (sentence on p. 5)

import Mathlib
import Definitions.Def_SteinbergFalse_Counterexample_NoFourFiveCycle
import Definitions.Def_SteinbergFalse_Counterexample_G

namespace SteinbergFalse.Counterexample

/-- Proof of Theorem 3: the graph `G` of Figure 3 has no cycle of length four or five. -/
theorem G_noFourFiveCycle : NoFourFiveCycle G := by sorry

end SteinbergFalse.Counterexample
