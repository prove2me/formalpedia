-- Prove2me | Theorems.Thm_SantosHirsch_Counter_theorem_1_6
-- name    : SantosHirsch.Counter.theorem_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:54:56.513593+00:00
-- url     : https://prove2.me/theorems/9fe4ddb0-9b1e-4d0e-ad3f-8a831c674b3c
-- title:
--   Theorem 1.6 — a 5-dimensional spindle with 48 facets and 322 vertices, of length six
-- statement:
--   There exist $a_1,\dots,a_{48}\in\mathbb R^5$, $b\in\mathbb R^{48}$ and points $u,v\in\mathbb R^5$ such that $P=\{x:\langle a_i,x\rangle\le b_i\}$ satisfies:
--
--   1. $P$ is bounded and $(a,b)$ is a facet presentation, so $P$ is a 5-polytope with 48 facets;
--   2. $P$ is a spindle with apices $u,v$ (every facet contains exactly one of them);
--   3. $P$ has exactly 322 vertices;
--   4. the graph distance between $u$ and $v$ is exactly six.
--
--   This is the second ingredient of Santos's disproof: a spindle whose length exceeds its dimension, to be fed to the strong $d$-step theorem.
--
--   **Formalization Note** "Length six" is exact: a 6-step walk from $u$ to $v$ exists and no walk with fewer steps exists (walks may pause, platform `Hirsch.Reach`).
-- source:
--   Santos, A counterexample to the Hirsch conjecture, arXiv:1006.2814v3, p. 4, Theorem 1.6

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace SantosHirsch.Counter

/-- Theorem 1.6 (p. 4): there is a 5-dimensional spindle with 48 facets and 322 vertices
whose apices are at graph distance exactly six. -/
theorem theorem_1_6 :
    ∃ (a : Fin 48 → EuclideanSpace ℝ (Fin 5)) (b : Fin 48 → ℝ)
      (u v : EuclideanSpace ℝ (Fin 5)),
      Bornology.IsBounded (Hirsch.Hpoly a b) ∧
      IsFacetPresentation a b ∧
      IsSpindle a b u v ∧
      (Set.extremePoints ℝ (Hirsch.Hpoly a b)).ncard = 322 ∧
      Hirsch.Reach (Hirsch.Hpoly a b) 6 u v ∧
      ∀ k < 6, ¬ Hirsch.Reach (Hirsch.Hpoly a b) k u v := by sorry

end SantosHirsch.Counter
