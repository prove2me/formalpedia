-- Prove2me | Theorems.Thm_ProjSchedMinCut_Transform_lemma_3
-- name    : ProjSchedMinCut.Transform.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:29.457593+00:00
-- url     : https://prove2.me/theorems/0029d34b-7951-4a74-beb9-cd536bb438ef
-- title:
--   Lemma 3, p. 8 — the image under (7) of a finite-capacity n-cut is feasible for (1)–(5), with w(x) = c(X, X̄)
-- statement:
--   Let $D$ be the minimum cut digraph of an instance of the project scheduling problem with start-time dependent costs $w_{jt} \ge 0$, and assume a feasible schedule exists. For each $n$-cut $(X, \bar X)$ of $D$ of finite capacity, the mapping (7) defines a feasible solution $x$ of the integer program (1)–(5), and
--   $$w(x) = c(X, \bar X).$$
--
--   Together with Lemma 2 and the injectivity of (7), this gives the one-to-one correspondence of Theorem 1.
--
--   **Formalization Note** Feasibility includes the window convention of p. 4 (variables outside $[e(j), \ell(j)]$ vanish). The capacity is compared with $w(x)$ through the embedding of $[0, \infty)$ into $[0, \infty]$.
-- source:
--   Möhring, Schulz, Stork & Uetz, Solving project scheduling problems by minimum cut computations, manuscript (July 2000, revised April 2002 and November 2002), p. 8, Lemma 3

import Mathlib
import Definitions.Def_ProjSchedMinCut_Transform_Setting

namespace ProjSchedMinCut.Transform

open Instance

/-- Lemma 3, p. 8: for each finite-capacity `n`-cut `(X, X̄)` of `D`, the mapping (7) defines a
feasible solution `x` of (1)–(5) with `w(x) = c(X, X̄)`. -/
theorem lemma_3 {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    ∀ X, I.IsNCut X → I.cutCap X < ⊤ →
      I.IPFeasible (I.xOfCut X) ∧ I.cutCap X = ENNReal.ofReal (I.cost (I.xOfCut X)) := by sorry

end ProjSchedMinCut.Transform
