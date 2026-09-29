-- Prove2me | Theorems.Thm_VectorSpaceOpt_exists_norming_functional
-- name    : VectorSpaceOpt.exists_norming_functional
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:50:04.16053+00:00
-- url     : https://prove2.me/theorems/c9987046-a90f-4cb9-950c-cf8919685128
-- title:
--   Existence of a norming functional
-- statement:
--   Let $x$ be a **nonzero** vector in a real normed vector space $X$. Then there is a bounded linear functional $F$ on $X$ with
--
--   $$\|F\| = 1 \qquad \text{and} \qquad F(x) = \|x\|,$$
--
--   that is, a unit-norm functional **aligned** with $x$.
--
--   The construction is one line given the previous corollary: define $f(\alpha x) = \alpha\|x\|$ on the one-dimensional subspace spanned by $x$, note that $\|f\| = 1$ there, and extend without increasing the norm.
--
--   The corollary is what makes the dual space large enough to be useful — it guarantees $X^*$ separates points of $X$, and it is the step behind the fact that the natural embedding of $X$ into its second dual is norm-preserving.
--
--   Its converse fails in general, even in Banach spaces: in $X = \ell_1$ with $X^* = \ell_\infty$, the functional $f(x) = \sum_i (1 - 1/i)\,\xi_i$ has $\|f\| = 1$, yet $f(x) < \|x\|$ for every nonzero $x$ — no vector is aligned with it. In reflexive spaces the converse does hold.
--
--   **Formalization Note.** The alignment condition is stated through the published `aligned` definition, $F(x) = \|F\|\,\|x\|$, rather than inlined. The hypothesis $x \neq 0$ is explicit: the source remarks that for $x = 0$ any bounded functional will do, but a unit-norm functional need not exist in a trivial space, so the claim is confined to nonzero $x$.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.4, Corollary 2, pp. 112–113

import Mathlib
import Definitions.Def_VectorSpaceOpt_aligned

namespace VectorSpaceOpt

theorem exists_norming_functional {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (x : X) (hx : x ≠ 0) :
    ∃ F : X →L[ℝ] ℝ, ‖F‖ = 1 ∧ VectorSpaceOpt_aligned x F := by sorry

end VectorSpaceOpt
