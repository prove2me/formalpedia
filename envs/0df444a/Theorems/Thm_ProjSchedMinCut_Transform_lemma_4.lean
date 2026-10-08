-- Prove2me | Theorems.Thm_ProjSchedMinCut_Transform_lemma_4
-- name    : ProjSchedMinCut.Transform.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:53.404344+00:00
-- url     : https://prove2.me/theorems/a22da96d-4290-44a9-b81a-d71c411c9e82
-- title:
--   Lemma 4, p. 8 — the capacity of a minimum a-b-cut equals the value of an optimal solution of (1)–(5)
-- statement:
--   Let $D$ be the minimum cut digraph of an instance of the project scheduling problem with start-time dependent costs $w_{jt} \ge 0$, and assume a feasible schedule exists. Then $D$ has a minimum $a$-$b$-cut, and for every minimum $a$-$b$-cut $(X, \bar X)$ there is an optimal solution $x$ of (1)–(5) with
--   $$c(X, \bar X) = w(x).$$
--
--   Hence the scheduling problem with start-time dependent costs can be solved by a single minimum cut computation.
--
--   **Formalization Note** The existence of a minimum cut (the digraph is finite) is made explicit so that the statement is not vacuous. The capacity is compared with $w(x)$ through the embedding of $[0,\infty)$ into $[0, \infty]$; in particular the minimum cut capacity is finite.
-- source:
--   Möhring, Schulz, Stork & Uetz, Solving project scheduling problems by minimum cut computations, manuscript (July 2000, revised April 2002 and November 2002), p. 8, Lemma 4

import Mathlib
import Definitions.Def_ProjSchedMinCut_Transform_Setting

namespace ProjSchedMinCut.Transform

open Instance

/-- Lemma 4, p. 8: a minimum `a`-`b`-cut of `D` exists, and the capacity of every minimum
`a`-`b`-cut equals the value `w(x)` of an optimal solution `x` of (1)–(5). -/
theorem lemma_4 {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    (∃ X, I.IsMinCut X) ∧
      ∀ X, I.IsMinCut X → ∃ x, I.IsOptimal x ∧ I.cutCap X = ENNReal.ofReal (I.cost x) := by sorry

end ProjSchedMinCut.Transform
