-- Prove2me | Theorems.Thm_SteinbergFalse_Counterexample_theorem_3
-- name    : SteinbergFalse.Counterexample.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:13.857982+00:00
-- url     : https://prove2.me/theorems/dc640f67-9767-4499-90d1-a71b1522837a
-- title:
--   Theorem 3 — there is a planar graph with no cycles of length four or five that is not 3-colorable
-- statement:
--   **Theorem 3** (Cohen-Addad, Hebdige, Král', Li, Salgado). There exists a finite planar graph $H$ such that
--
--   $$
--   H \text{ has no cycle of length } 4 \text{ or } 5 \qquad\text{and}\qquad \chi(H) > 3 .
--   $$
--
--   Steinberg conjectured in 1976 that every planar graph with no cycles of length four or five is 3-colorable. Theorem 3 is exactly the negation of that conjecture, so Steinberg's Conjecture is false.
--
--   **Formalization Note** The graph is a simple graph on the vertex set `Fin n` for some natural number $n$; this loses no generality, since every finite graph is isomorphic to one on `Fin n`. Planarity is the published straight-line planarity predicate `OPG37357.IsPlanar`, which for finite simple graphs is equivalent to planarity by Fáry's theorem and in any case implies topological planarity, so the statement is at least as strong as the paper's. "No cycles of length four or five" is the definition `NoFourFiveCycle` (cycles are Mathlib walks with `Walk.IsCycle`), and "not 3-colorable" is `¬ H.Colorable 3`. The empty graph cannot serve as a trivial witness, because it is 3-colorable.
-- source:
--   Cohen-Addad, Hebdige, Král', Li & Salgado, Steinberg's Conjecture is false, arXiv:1604.05108v2, p. 4, Theorem 3 (conjecture stated on p. 1)

import Mathlib
import Definitions.Def_opg37357_obstacle_number
import Definitions.Def_SteinbergFalse_Counterexample_NoFourFiveCycle

namespace SteinbergFalse.Counterexample

/-- Theorem 3 (Cohen-Addad, Hebdige, Král', Li, Salgado): there exists a planar graph with no
cycles of length four or five that is not 3-colorable. Planarity is straight-line planarity
`OPG37357.IsPlanar`; the graph is finite, on the vertex set `Fin n`. -/
theorem theorem_3 :
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      OPG37357.IsPlanar H ∧ NoFourFiveCycle H ∧ ¬ H.Colorable 3 := by sorry

end SteinbergFalse.Counterexample
