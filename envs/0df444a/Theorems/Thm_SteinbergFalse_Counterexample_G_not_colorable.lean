-- Prove2me | Theorems.Thm_SteinbergFalse_Counterexample_G_not_colorable
-- name    : SteinbergFalse.Counterexample.G_not_colorable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:40.339765+00:00
-- url     : https://prove2.me/theorems/cfc49aa6-1a4d-4422-9b8d-3fea57738033
-- title:
--   Proof of Theorem 3 — the graph $G$ of Figure 3 has no 3-coloring
-- statement:
--   Let $G$ be the 166-vertex graph of Figure 3. Then $G$ has no proper coloring with three colors:
--
--   $$
--   \chi(G) > 3 .
--   $$
--
--   This is the second property of $G$ established in the proof of Theorem 3: it is what makes $G$ a counterexample to Steinberg's Conjecture.
--
--   **Formalization Note** "No 3-coloring" is Mathlib's `¬ G.Colorable 3`: there is no map from the vertices to a set of three colors that differs on adjacent vertices.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 5, proof of Theorem 3

import Mathlib
import Definitions.Def_SteinbergFalse_Counterexample_G

namespace SteinbergFalse.Counterexample

/-- Proof of Theorem 3: the graph `G` of Figure 3 has no 3-coloring. -/
theorem G_not_colorable : ¬ G.Colorable 3 := by sorry

end SteinbergFalse.Counterexample
