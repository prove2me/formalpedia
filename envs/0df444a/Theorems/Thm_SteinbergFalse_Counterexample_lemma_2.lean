-- Prove2me | Theorems.Thm_SteinbergFalse_Counterexample_lemma_2
-- name    : SteinbergFalse.Counterexample.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:13:26.527984+00:00
-- url     : https://prove2.me/theorems/a0c36a97-abb5-42d3-9ad4-9c86f79586df
-- title:
--   Lemma 2 — $G_2$ has no 4- or 5-cycle, no 3-coloring makes $a,b,c$ one color, and the contacts are pairwise at distance 4
-- statement:
--   Let $G_2$ be the 42-vertex graph of Figure 2 (three copies of $G_1$ pasted together), with contact vertices $a$, $b$, $c$. Then:
--
--   1. $G_2$ has no cycle of length four or five;
--   2. there is no proper 3-coloring $\varphi$ of $G_2$ with $\varphi(a) = \varphi(b) = \varphi(c)$;
--   3. any two of the contact vertices are at distance four:
--   $$
--   d_{G_2}(a,b) = d_{G_2}(a,c) = d_{G_2}(b,c) = 4 .
--   $$
--
--   This is the second step of the construction: four copies of $G_2$ are pasted together to form the counterexample $G$ of Theorem 3.
--
--   **Formalization Note** A 3-coloring is a Mathlib `G2.Coloring (Fin 3)`. Item 2 does not exclude colorings in which two of the contact vertices share a color. The distance is `SimpleGraph.dist`, whose junk value $0$ for unreachable pairs is never hit, because each asserted distance is positive.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 3, Lemma 2

import Mathlib
import Definitions.Def_SteinbergFalse_Counterexample_NoFourFiveCycle
import Definitions.Def_SteinbergFalse_Counterexample_G2

namespace SteinbergFalse.Counterexample

/-- Lemma 2: the graph `G₂` of Figure 2 has no cycles of length four or five; no 3-coloring of
`G₂` gives the three contact vertices a, b, c (= 0, 1, 2) the same color; and the distance
between any two of a, b, c is four. -/
theorem lemma_2 :
    NoFourFiveCycle G2 ∧
      (∀ C : G2.Coloring (Fin 3), ¬ (C G2.a = C G2.b ∧ C G2.b = C G2.c)) ∧
      G2.dist G2.a G2.b = 4 ∧ G2.dist G2.a G2.c = 4 ∧ G2.dist G2.b G2.c = 4 := by sorry

end SteinbergFalse.Counterexample
