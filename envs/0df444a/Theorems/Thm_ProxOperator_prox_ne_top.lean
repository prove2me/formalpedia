-- Prove2me | Theorems.Thm_ProxOperator_prox_ne_top
-- name    : ProxOperator.prox_ne_top
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:22:31.101761+00:00
-- url     : https://prove2.me/theorems/eb94c9df-58b4-4c48-8475-8cc729c4b84e
-- title:
--   The proximal map of a proper closed convex function lands where the function is finite
-- statement:
--   Let $H$ be a real inner product space, let $f : H \to \overline{\mathbb{R}}$ be proper, closed and convex, let $\gamma \in \mathbb{R}$, and let $P$ satisfy the defining property of the proximal map $\operatorname{prox}_{\gamma f}$. Then for every $x \in H$,
--
--   $$
--   f(P x) \;\neq\; +\infty .
--   $$
--
--   In words: the proximal map never leaves the domain of $f$. The reason is immediate from the
--   variational characterization -- $P x$ minimizes
--   $f(\cdot) + \tfrac{1}{2\gamma}\|\cdot - x\|^2$, and properness provides some point $x_0$ with
--   $f(x_0)$ finite, so the minimum value is finite and $f(Px)$ cannot be $+\infty$.
--
--   Every subsequent estimate on a splitting iterate depends on this: the iterates of a proximal or
--   splitting method are images of proximal maps, and an objective bound at such a point is
--   vacuous until one knows the objective is finite there. Properness also gives
--   $f \neq -\infty$ everywhere, so together the two make $f(Px)$ a genuine real number.
--
--   **Formalization Note** `IsProx γ f P` is stated as the inequality
--   $f(Px) + \tfrac{1}{2\gamma}\|Px - x\|^2 \le f(y) + \tfrac{1}{2\gamma}\|y - x\|^2$ for all $y$,
--   which is what the proof instantiates at the properness witness $x_0$; $\gamma$ is not required
--   to be positive, since only the comparison at one point is used.
-- source:
--   The finiteness step used throughout Davis & Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017) 829-858, DOI 10.1007/s11228-017-0421-z, proof of Theorem 3.2, pp. 839-840; isolated here as a consequence of the defining inequality of the proximal map.

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_ConvexRates_Algorithm

namespace ProxOperator

/-- The proximal map of a proper closed convex `EReal`-valued function lands where the
function is finite. -/
theorem prox_ne_top {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (f : H → EReal) (P : H → H)
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f)
    (hP : ThreeOpSplitting.ConvexRates.IsProx γ f P) (x : H) :
    f (P x) ≠ ⊤ := by sorry

end ProxOperator
