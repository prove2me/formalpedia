-- Prove2me | Theorems.Thm_SantosHirsch_Counter_corollary_1_7
-- name    : SantosHirsch.Counter.corollary_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:55:35.206458+00:00
-- url     : https://prove2.me/theorems/d3960eed-0d4b-4307-aa8f-4e3f7f3797a6
-- title:
--   Corollary 1.7 — there is a non-Hirsch polytope of dimension 43 with 86 facets
-- statement:
--   There exist $a_1,\dots,a_{86}\in\mathbb R^{43}$ and $b\in\mathbb R^{86}$ such that the polytope
--   $$P=\{x\in\mathbb R^{43}:\ \langle a_i,x\rangle\le b_i,\ i=1,\dots,86\}$$
--   is nonempty and bounded, its 86 inequalities form a facet presentation (nonempty interior, no redundant inequality, so $P$ has dimension 43 and exactly 86 facets), and the combinatorial diameter of $P$ is greater than $86-43=43$.
--
--   This is the main result of Santos's paper: it disproves the Hirsch conjecture, which asserted that a $d$-polytope with $n$ facets has diameter at most $n-d$.
--
--   **Formalization Note** The combinatorial diameter is that of the vertex-edge graph, where edges are the one-dimensional faces (platform `Hirsch.DiamLE`). Non-Hirsch is "the diameter is not at most $n-d$". Santos remarks (p. 24) that the polytope has diameter 44, but the corollary claims only non-Hirsch, and so does this statement.
-- source:
--   Santos, A counterexample to the Hirsch conjecture, arXiv:1006.2814v3, p. 4, Corollary 1.7

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace SantosHirsch.Counter

/-- Corollary 1.7 (p. 4): there is a non-Hirsch polytope of dimension 43 with 86 facets. -/
theorem corollary_1_7 :
    ∃ (a : Fin 86 → EuclideanSpace ℝ (Fin 43)) (b : Fin 86 → ℝ),
      (Hirsch.Hpoly a b).Nonempty ∧
      Bornology.IsBounded (Hirsch.Hpoly a b) ∧
      IsFacetPresentation a b ∧
      IsNonHirsch a b := by sorry

end SantosHirsch.Counter
