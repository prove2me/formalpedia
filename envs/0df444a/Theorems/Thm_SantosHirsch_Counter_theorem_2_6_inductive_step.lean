-- Prove2me | Theorems.Thm_SantosHirsch_Counter_theorem_2_6_inductive_step
-- name    : SantosHirsch.Counter.theorem_2_6_inductive_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:55:21.001025+00:00
-- url     : https://prove2.me/theorems/e38f932e-5c95-4beb-9a43-43ee8ce34611
-- title:
--   Proof of Theorem 2.6, inductive step (polar form) — one more dimension, one more facet, length at least one more
-- statement:
--   Let $d,n,l$ be natural numbers with $n>2d$. Let $P=\{x\in\mathbb R^d:\langle a_i,x\rangle\le b_i,\ i=1,\dots,n\}$ be bounded, with $(a,b)$ a facet presentation (so $P$ is a $d$-polytope with $n$ facets), and suppose $P$ is a spindle with apices $u,v$ whose length is at least $l$ (no walk of fewer than $l$ steps joins $u$ and $v$ in the graph of $P$). Then there is a bounded facet presentation $(a',b')$ with $n+1$ rows in $\mathbb R^{d+1}$ and points $u',v'$ such that $P'=\mathrm{Hpoly}(a',b')$ is a spindle with apices $u',v'$ of length at least $l+1$.
--
--   Iterating this step $n-2d$ times is how Santos proves the strong $d$-step theorem (Theorem 1.5): each step lowers the "asimpliciality" $n-2d$ by one and raises the length by at least one.
--
--   **Formalization Note** Santos states the step for prismatoids: "We call the number $s = n - 2d$ the asimpliciality of $Q$"; if $s>0$ one builds $\tilde Q$ with dimension one higher, one vertex more, and width at least one more. In the polar, vertices of $Q$ are facets of the spindle and the width is the length, so $s>0$ is $n>2d$. "Length $l$" is read as "length at least $l$", equivalent by monotonicity and the form the induction uses. The platform's `Hirsch.spindle_one_step` covers only width $>d$ and has no facet presentation.
-- source:
--   Santos, A counterexample to the Hirsch conjecture, arXiv:1006.2814v3, p. 9, proof of Theorem 2.6, inductive step

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_SantosHirsch_Counter_Setting

open scoped RealInnerProductSpace

namespace SantosHirsch.Counter

/-- Inductive step of the proof of Theorem 2.6 (p. 9), polar form: a `d`-spindle with `n`
facets, `n > 2d`, and length at least `l` yields a `(d+1)`-spindle with `n+1` facets and
length at least `l+1`. -/
theorem theorem_2_6_inductive_step (d n l : ℕ) (hs : 2 * d < n)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hirsch.Hpoly a b))
    (hfp : IsFacetPresentation a b)
    (hsp : IsSpindle a b u v)
    (hl : ∀ k < l, ¬ Hirsch.Reach (Hirsch.Hpoly a b) k u v) :
    ∃ (a' : Fin (n + 1) → EuclideanSpace ℝ (Fin (d + 1))) (b' : Fin (n + 1) → ℝ)
      (u' v' : EuclideanSpace ℝ (Fin (d + 1))),
      Bornology.IsBounded (Hirsch.Hpoly a' b') ∧
      IsFacetPresentation a' b' ∧
      IsSpindle a' b' u' v' ∧
      ∀ k < l + 1, ¬ Hirsch.Reach (Hirsch.Hpoly a' b') k u' v' := by sorry

end SantosHirsch.Counter
