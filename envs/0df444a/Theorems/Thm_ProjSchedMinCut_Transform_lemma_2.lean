-- Prove2me | Theorems.Thm_ProjSchedMinCut_Transform_lemma_2
-- name    : ProjSchedMinCut.Transform.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:10:36.626842+00:00
-- url     : https://prove2.me/theorems/0446cf78-37a6-4f5f-bcd5-2c323831b903
-- title:
--   Lemma 2, p. 8 — every feasible solution of (1)–(5) is the image under (7) of an n-cut with c(X, X̄) = w(x)
-- statement:
--   Let $D$ be the minimum cut digraph of an instance of the project scheduling problem with start-time dependent costs $w_{jt} \ge 0$, and assume a feasible schedule exists. For each feasible solution $x$ of the integer program (1)–(5) there exists an $n$-cut $(X, \bar X)$ of $D$ of finite capacity such that $x$ is the image of $(X, \bar X)$ under the mapping (7), and
--   $$w(x) = c(X, \bar X).$$
--
--   This is the surjectivity half of Theorem 1.
--
--   **Formalization Note** Finiteness of $c(X, \bar X)$ is stated explicitly; it also follows from $c(X, \bar X) = w(x)$, since $w(x)$ is a real number. The capacity is compared with $w(x)$ through the embedding of $[0, \infty)$ into $[0, \infty]$.
-- source:
--   Möhring, Schulz, Stork & Uetz, Solving project scheduling problems by minimum cut computations, manuscript (July 2000, revised April 2002 and November 2002), p. 8, Lemma 2

import Mathlib
import Definitions.Def_ProjSchedMinCut_Transform_Setting

namespace ProjSchedMinCut.Transform

open Instance

/-- Lemma 2, p. 8: every feasible solution `x` of (1)–(5) is the image under (7) of an `n`-cut
`(X, X̄)` of `D` (necessarily of finite capacity), and `w(x) = c(X, X̄)`. -/
theorem lemma_2 {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    ∀ x, I.IPFeasible x →
      ∃ X, I.IsNCut X ∧ I.cutCap X < ⊤ ∧ I.xOfCut X = x ∧
        I.cutCap X = ENNReal.ofReal (I.cost x) := by sorry

end ProjSchedMinCut.Transform
