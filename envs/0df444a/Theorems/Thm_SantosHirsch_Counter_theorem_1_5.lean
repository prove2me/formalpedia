-- Prove2me | Theorems.Thm_SantosHirsch_Counter_theorem_1_5
-- name    : SantosHirsch.Counter.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:55:28.788218+00:00
-- url     : https://prove2.me/theorems/544c51f4-1af4-4063-bf93-e384e1829a30
-- title:
--   Theorem 1.5 (Strong d-step Theorem for spindles) — length l becomes length ≥ l + n − 2d in dimension n − d
-- statement:
--   Let $P=\{x\in\mathbb R^d:\langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ be bounded, with $(a,b)$ a facet presentation (so $P$ is a $d$-polytope with $n$ facets), and let $P$ be a spindle with apices $u,v$ of length at least $l$. Then there exist $2n-2d$ inequalities in $\mathbb R^{n-d}$, forming a bounded facet presentation of a polytope $P'$, and points $u',v'$, such that $P'$ is a spindle with apices $u',v'$ of length at least
--   $$l+n-2d.$$
--   Moreover, if $l>d$, then $P'$ is non-Hirsch: its diameter exceeds $(2n-2d)-(n-d)=n-d$.
--
--   This is the first ingredient of Santos's disproof; with the 5-spindle of length six of Theorem 1.6 ($d=5$, $n=48$, $l=6$) it gives a non-Hirsch polytope of dimension 43 with 86 facets. The platform already has the "in particular" clause in a weaker form, `Hirsch.strong_dstep_spindle` (Proved), which counts rows instead of facets and does not assert that $P'$ is a spindle or the length bound $l+n-2d$.
--
--   **Formalization Note** "Length $l$" is read as "length at least $l$" (no walk of fewer than $l$ steps), which is equivalent by monotonicity of walks with pauses and is the form the proof uses. The natural-number expressions $n-d$, $2n-2d$ and $l+(n-2d)$ are the real ones because a spindle has $n\ge 2d$ (platform `Hirsch.spindle_n_ge_two_d`). Non-Hirsch is stated as "diameter not at most $(2n-2d)-(n-d)$".
-- source:
--   Santos, A counterexample to the Hirsch conjecture, arXiv:1006.2814v3, p. 4, Theorem 1.5 (equivalently Theorem 2.6, p. 9)

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace SantosHirsch.Counter

/-- Theorem 1.5 (Strong d-step Theorem for spindles, p. 4): a `d`-spindle with `n` facets
and length (at least) `l` yields an `(n-d)`-spindle with `2n-2d` facets and length at least
`l + n - 2d`; if moreover `l > d`, the new spindle is non-Hirsch. -/
theorem theorem_1_5 (d n l : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b))
    (hfp : IsFacetPresentation a b)
    (hsp : IsSpindle a b u v)
    (hl : ∀ k < l, ¬ Hirsch.Reach (Hirsch.Hpoly a b) k u v) :
    ∃ (a' : Fin (2 * n - 2 * d) → EuclideanSpace ℝ (Fin (n - d)))
      (b' : Fin (2 * n - 2 * d) → ℝ) (u' v' : EuclideanSpace ℝ (Fin (n - d))),
      Bornology.IsBounded (Hirsch.Hpoly a' b') ∧
      IsFacetPresentation a' b' ∧
      IsSpindle a' b' u' v' ∧
      (∀ k < l + (n - 2 * d), ¬ Hirsch.Reach (Hirsch.Hpoly a' b') k u' v') ∧
      (d < l → IsNonHirsch a' b') := by sorry

end SantosHirsch.Counter
