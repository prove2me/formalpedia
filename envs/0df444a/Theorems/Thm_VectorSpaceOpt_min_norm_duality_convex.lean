-- Prove2me | Theorems.Thm_VectorSpaceOpt_min_norm_duality_convex
-- name    : VectorSpaceOpt.min_norm_duality_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:54:38.786115+00:00
-- url     : https://prove2.me/theorems/e1b77b92-ed44-467e-bd1e-f8263bf2a394
-- title:
--   Minimum norm duality for convex sets
-- statement:
--   This extends the duality principle for minimum norm problems from subspaces and linear varieties to arbitrary convex sets.
--
--   Let $K$ be a convex set in a real normed vector space $X$, with **support functional**
--
--   $$h(x^*) = \sup_{k \in K}\, \langle k, x^*\rangle,$$
--
--   and let $x_1 \in X$ be at distance $d > 0$ from $K$. Then
--
--   $$d \;=\; \inf_{x \in K} \|x - x_1\| \;=\; \max_{\|x^*\| \le 1}\ \big[\langle x_1, x^*\rangle - h(x^*)\big],$$
--
--   the maximum being **achieved** by some $x_0^*$. If the infimum on the left is achieved by some $x_0 \in K$, then $-x_0^*$ is **aligned** with $x_0 - x_1$.
--
--   The geometric content is visible in one sentence: the minimum distance from a point to a convex set equals the maximum of the distances from that point to hyperplanes separating the point from the set. Given $x^*$ of unit norm, the hyperplane $\{x : \langle x, x^*\rangle = h(x^*)\}$ supports $K$, and $\langle x_1, x^*\rangle - h(x^*)$ is exactly the distance from $x_1$ to it; the separating hyperplanes are supplied by Eidelheit's theorem, and the best of them realizes the distance.
--
--   The subspace duality theorem is the special case $K = M$, where $h$ is $0$ on $M^\perp$ and $+\infty$ elsewhere, so the maximization collapses onto the unit ball of $M^\perp$. The result is subsumed in turn by the theory of conjugate convex functionals in Chapter 7.
--
--   **Formalization Note.** The support functional is the published definition, valued in the extended reals since the supremum may be $+\infty$ (it is $+\infty$ exactly when $K$ is unbounded in the direction of $x^*$, in which case $\langle x_1, x^*\rangle - h(x^*) = -\infty$ and that $x^*$ is simply not a contender). The maximum is therefore stated as an extended-real equality for the witness together with an extended-real upper bound for every competitor. The distance is an infimum over $K$, and $d > 0$ is hypothesized as in the source; alignment uses the published `aligned` definition applied to $-x_0^*$.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.13, Theorem 1, p. 136

import Mathlib
import Definitions.Def_VectorSpaceOpt_aligned
import Definitions.Def_VectorSpaceOpt_support_functional

namespace VectorSpaceOpt

theorem min_norm_duality_convex {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (K : Set X) (hK : Convex ℝ K) (hne : K.Nonempty)
    (x₁ : X) (hd : 0 < ⨅ x : K, ‖(x : X) - x₁‖) :
    ∃ f₀ : X →L[ℝ] ℝ, ‖f₀‖ ≤ 1 ∧
      ((f₀ x₁ : EReal) - VectorSpaceOpt_support_functional K f₀
        = ((⨅ x : K, ‖(x : X) - x₁‖ : ℝ) : EReal)) ∧
      (∀ f : X →L[ℝ] ℝ, ‖f‖ ≤ 1 →
        (f x₁ : EReal) - VectorSpaceOpt_support_functional K f
          ≤ ((⨅ x : K, ‖(x : X) - x₁‖ : ℝ) : EReal)) ∧
      (∀ x₀ ∈ K, ‖x₀ - x₁‖ = (⨅ x : K, ‖(x : X) - x₁‖) →
        VectorSpaceOpt_aligned (x₀ - x₁) (-f₀)) := by sorry

end VectorSpaceOpt
