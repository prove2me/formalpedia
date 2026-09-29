-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_concaveClosure_concaveOn
-- name    : SteinitzExchange.Extension.concaveClosure_concaveOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T16:49:23.405196+00:00
-- url     : https://prove2.me/theorems/3365fe25-4050-4f6f-9427-b85569f25bd9
-- title:
--   The concave closure $\hat g$ is a concave function on $\overline B$
-- statement:
--   Let $B\subseteq \mathbb Z^V$ be a nonempty finite set and $g:B\to\mathbb R$ any function. Define the concave conjugate and the concave closure by
--
--   $$g^\circ(p) = \min\{\langle p,x\rangle - g(x) : x\in B\}, \qquad \hat g(b) = \inf\{\langle p,b\rangle - g^\circ(p) : p\in\mathbb R^V\}\quad (b\in\overline B).$$
--
--   Then $\hat g$ is **concave on the convex hull** $\overline B$: $\overline B$ is convex, and for all $x,y\in\overline B$ and all $a,b\ge 0$ with $a+b=1$,
--
--   $$a\,\hat g(x) + b\,\hat g(y) \;\le\; \hat g\big(a\,x + b\,y\big).$$
--
--   **Why this holds.** $\hat g$ is an infimum of the affine functions $L_p(b) = \langle p, b\rangle - g^\circ(p)$, indexed by $p\in\mathbb R^V$. Since $a,b\ge 0$ the infimum may be pulled through the weighted sums, giving an upper bound, and for each fixed $p$ the functional $b \mapsto aL_p(x) + bL_p(y)$ is affine with value $L_p(a x + b y)$ at the point $a x + b y$. Therefore
--
--   $$a\,\hat g(x) + b\,\hat g(y) \le \inf_p\big(aL_p(x) + bL_p(y)\big) = \inf_p L_p(a x + b y) = \hat g(a x + b y),$$
--
--   which is exactly the concavity inequality. The concavity of $\overline B$ itself is automatic, being a convex hull.
--
--   No exchange property is assumed: this holds for every $g$, which is why it is the purely convex-analytic half of the Extension Theorem. Combined with the fact that $\hat g$ agrees with an M-concave $\omega$ on $B$, it exhibits $\hat g$ as a concave extension of $\omega$ to $\overline B$.
--
--   **Formalization Note.** $\hat g$ is a total function on $\mathbb R^V$ but the concavity is asserted only on $\overline B$, where the defining infimum is bounded below, so the values off $\overline B$ (where the real infimum is a junk value) are irrelevant. `ConcaveOn ℝ (hull B) (concaveClosure B g)` is Mathlib's `ConcaveOn` for the scalar field $\mathbb R$.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 284, Eq. (4.2)

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 284, Eq. (4.2): the concave closure `ĝ(b) = inf{⟨p, b⟩ − g°(p) | p ∈ ℝ^V}` of a function
`g : B → ℝ` on a nonempty finite `B ⊆ ℤ^V` is a concave function on the convex hull `B̄` of `B`.

This is the concavity half of the Extension Theorem (Murota 1996, p. 288, Theorem 4.6): together with
`concaveClosure_eq_of_exc` (Lemma 4.5) it shows that an M-concave `ω` on an integral base set
`B` extends to a genuinely concave `ω̄ = ĝ` on `B̄` agreeing with `ω` on `B`.

The statement is the standard fact that an infimum of affine functions is concave, since each
`b ↦ ⟨p, b⟩ − g°(p)` is affine in `b` and the concavity inequality is preserved under infima:
for `a + b = 1` with `a, b ≥ 0`,
$$a \cdot ĝ(x) + b \cdot ĝ(y) \le \inf_p \big(a\cdot(\langle p, x\rangle - g^\circ(p)) + b \cdot (\langle p, y\rangle - g^\circ(p))\big) = ĝ(a\cdot x + b\cdot y),$$
using `a ≥ 0` and `b ≥ 0` to pull the infimum through the weighted sums. No exchange property is assumed;
this is a property of the construction for every `g`. -/
theorem concaveClosure_concaveOn {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) :
    ConcaveOn ℝ (hull B) (concaveClosure B g) := by sorry

end SteinitzExchange.Extension
