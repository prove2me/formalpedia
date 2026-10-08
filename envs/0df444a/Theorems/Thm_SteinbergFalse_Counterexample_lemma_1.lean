-- Prove2me | Theorems.Thm_SteinbergFalse_Counterexample_lemma_1
-- name    : SteinbergFalse.Counterexample.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:53.562974+00:00
-- url     : https://prove2.me/theorems/37940f82-44ab-430b-bf4c-bfdf311da517
-- title:
--   Lemma 1 — $G_1$ has no 4- or 5-cycle, no 3-coloring makes $a,b,c$ one color, and $d(a,b)=d(a,c)=3$, $d(b,c)=4$
-- statement:
--   Let $G_1$ be the 15-vertex graph of Figure 1, with contact vertices $a$, $b$, $c$. Then:
--
--   1. $G_1$ has no cycle of length four or five;
--   2. there is no proper 3-coloring $\varphi$ of $G_1$ with $\varphi(a) = \varphi(b) = \varphi(c)$;
--   3. the graph distances between the contact vertices are
--   $$
--   d_{G_1}(a,b) = 3, \qquad d_{G_1}(a,c) = 3, \qquad d_{G_1}(b,c) = 4 .
--   $$
--
--   This is the first step of the construction: it is used, three times, to obtain the corresponding properties of $G_2$ in Lemma 2.
--
--   **Formalization Note** A 3-coloring is a Mathlib `G1.Coloring (Fin 3)`, i.e. a map to three colors that differs on adjacent vertices. Item 2 says that no coloring gives all three contact vertices one color; it does not exclude colorings in which two of them share a color. The distance is `SimpleGraph.dist`, which takes the junk value $0$ for unreachable pairs; since every asserted distance is positive, each equality also asserts that the two vertices are connected.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 2, Lemma 1

import Mathlib
import Definitions.Def_SteinbergFalse_Counterexample_NoFourFiveCycle
import Definitions.Def_SteinbergFalse_Counterexample_G1

namespace SteinbergFalse.Counterexample

/-- Lemma 1: the graph `G₁` of Figure 1 has no cycles of length four or five; no 3-coloring of
`G₁` gives the three contact vertices a, b, c (= 0, 1, 2) the same color; and
dist(a, b) = 3, dist(a, c) = 3, dist(b, c) = 4. -/
theorem lemma_1 :
    NoFourFiveCycle G1 ∧
      (∀ C : G1.Coloring (Fin 3), ¬ (C G1.a = C G1.b ∧ C G1.b = C G1.c)) ∧
      G1.dist G1.a G1.b = 3 ∧ G1.dist G1.a G1.c = 3 ∧ G1.dist G1.b G1.c = 4 := by sorry

end SteinbergFalse.Counterexample
