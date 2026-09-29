-- Prove2me | Theorems.Thm_SteinitzExchange_LocalSupermod_argmax_hull_subset
-- name    : SteinitzExchange.LocalSupermod.argmax_hull_subset
-- status  : Open
-- author  : @WillR
-- created : 2026-09-28T15:29:18.405593+00:00
-- url     : https://prove2.me/theorems/13297295-3a5e-43d2-91f4-c5ec1290037b
-- title:
--   Lemma 4.3 (integrally convex argmax) — every integer point of conv(argmax B g) lies in argmax B g
-- statement:
--   Let $B \subseteq \mathbb{Z}^V$ be finite, let $g : \mathbb{Z}^V \to \mathbb{R}$ be any function, and let $A = \operatorname{argmax} B g = \{x \in B \mid g(x) \ge g(y)\ \forall y \in B\}$. Then every integer point $z$ of the convex hull $\overline{A}$ of $A$ in $\mathbb{R}^V$ lies in $A$: $z \in \mathbb{Z}^V$ and $z \in \overline{A}$ imply $z \in A$. This is the integrally-convexity of a maximiser set for a linear functional, used as the hypothesis $h_{\mathrm{conv}}$ of Theorem 5.1 when that theorem is instantiated at an argmax set. The statement needs no base-set hypothesis: it is a statement purely about maximisers of one function on a finite set.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 285, Lemma 4.3

import Mathlib
import Definitions.Def_SteinitzExchange_LocalSupermod_IntegralBaseSet
import Definitions.Def_SteinitzExchange_LocalSupermod_Exchange

namespace SteinitzExchange.LocalSupermod

/-- The maximiser set of a linear functional on a finite `B` is integrally convex: every
integer point of its convex hull is again a maximiser. This is the "argmax is an integral
base polytope" reading of Murota 1996, p. 285, Lemma 4.3, and it is the hypothesis
`hconv` that Theorem 5.1 (`baseSet_iff_support_matroidal`) needs when it is instantiated at the
argmax set. For `A = argmax B g` the claim is that every integer point of the convex hull `hull A`
lies in `A`; no base-set hypothesis is required for the inclusion itself. -/
theorem argmax_hull_subset {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset (V → ℤ)) (g : (V → ℤ) → ℝ) (z : V → ℤ) :
    toReal z ∈ hull (argmaxB B g) → z ∈ argmaxB B g := by sorry

end SteinitzExchange.LocalSupermod
