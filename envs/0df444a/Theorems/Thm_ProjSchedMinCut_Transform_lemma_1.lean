-- Prove2me | Theorems.Thm_ProjSchedMinCut_Transform_lemma_1
-- name    : ProjSchedMinCut.Transform.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:52.884498+00:00
-- url     : https://prove2.me/theorems/676ca2b8-21bf-49b0-9238-87e2616fa914
-- title:
--   Lemma 1, p. 6 — every minimum a-b-cut of D has an n-cut of the same capacity
-- statement:
--   Let $D = (V, A)$ be the minimum cut digraph of an instance of the project scheduling problem with start-time dependent costs $w_{jt} \ge 0$, and assume a feasible schedule exists. If $(X, \bar X)$ is a minimum $a$-$b$-cut of $D$, then there exists an $n$-cut $(X^*, \bar X^*)$ of $D$ with
--   $$c(X^*, \bar X^*) = c(X, \bar X).$$
--
--   Recall that an $n$-cut is an $a$-$b$-cut in which, for every job, exactly one assignment arc is in the cut. The lemma shows that restricting attention to $n$-cuts loses nothing when computing a minimum cut, which is what makes the minimum cut value equal to the optimal scheduling cost.
--
--   **Formalization Note** Only the first sentence of Lemma 1 is formalized; its second sentence, that $(X^*, \bar X^*)$ can be computed from $(X, \bar X)$ in time $O(nT)$, is a running-time claim and is omitted. As in the paper, no finiteness of $c(X, \bar X)$ is assumed. Capacities are in $[0, \infty]$.
-- source:
--   Möhring, Schulz, Stork & Uetz, Solving project scheduling problems by minimum cut computations, manuscript (July 2000, revised April 2002 and November 2002), p. 6, Lemma 1

import Mathlib
import Definitions.Def_ProjSchedMinCut_Transform_Setting

namespace ProjSchedMinCut.Transform

open Instance

/-- Lemma 1, p. 6: for every minimum `a`-`b`-cut `(X, X̄)` of `D` there is an `n`-cut
`(X*, X̄*)` of `D` with the same capacity. -/
theorem lemma_1 {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    ∀ X, I.IsMinCut X → ∃ Xs, I.IsNCut Xs ∧ I.cutCap Xs = I.cutCap X := by sorry

end ProjSchedMinCut.Transform
