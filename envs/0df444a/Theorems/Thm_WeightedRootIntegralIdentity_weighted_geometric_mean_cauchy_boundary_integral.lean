-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_geometric_mean_cauchy_boundary_integral
-- name    : WeightedRootIntegralIdentity.weighted_geometric_mean_cauchy_boundary_integral
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T18:55:58.331304+00:00
-- url     : https://prove2.me/theorems/d77e1751-d45e-40a4-8d84-98ce40f8bcb9
-- title:
--   Cauchy boundary-integral form of the weighted geometric mean
-- statement:
--   Let $n\ge 2$, let $0<a_0\le a_1\le\cdots\le a_{n-1}$, and let $w_0,\ldots,w_{n-1}>0$ satisfy $\sum_{i=0}^{n-1}w_i=1$. Write $z^{w}$ for the principal power $\exp(w\operatorname{Log} z)$. Then
--
--   $$\frac1\pi\int_{a_0}^{a_{n-1}}
--   \frac{\operatorname{Im}\prod_{i=0}^{n-1}(x-a_i)^{w_i}}{x}\,dx
--   =\sum_{i=0}^{n-1}w_ia_i-\prod_{i=0}^{n-1}a_i^{w_i}.$$
--
--   This is the analytic core of the weighted geometric-mean integral representation, written in terms of the boundary values of $F(z)=\prod_{i=0}^{n-1}(z-a_i)^{w_i}$ on the slit $[a_0,a_{n-1}]$. The function $F$ is holomorphic off that slit, is real and negative on $(-\infty,a_0)$ with $F(0)=-\prod_i a_i^{w_i}$, and satisfies $F(z)=z-\sum_i w_ia_i+O(1/z)$ as $z\to\infty$, because $\sum_i w_i=1$. Applying the residue theorem to $F(z)/z$ on a large circle, and collapsing the contour onto the pole at the origin together with the two sides of the slit, converts the coefficient comparison into exactly the displayed identity: the circle contributes $-\sum_i w_ia_i$, the pole contributes the residue $F(0)=-\prod_i a_i^{w_i}$, and the slit contributes the integral of the jump $2i\operatorname{Im}F$ divided by $x$.
--
--   Together with the boundary-value formula for $\operatorname{Im}F$ on each gap $(a_k,a_{k+1})$, this yields the sine-weighted sum of interval integrals in the weighted geometric-mean integral identity.
-- source:
--   Feng Qi, Xiao-Jing Zhang, and Wen-Hui Li, An integral representation for the weighted geometric mean and its applications, Acta Mathematica Sinica (English Series) 30 (2014), Theorem 3.1 (case z = 0); the identity is summarized as equation (4) at https://math.stackexchange.com/questions/4244874/can-we-prove-am-gm-inequality-using-these-integrals . This statement is one of the two steps of the standard contour-integral proof of that theorem, introduced here as a lemma in the decomposition of WeightedRootIntegralIdentity.weighted_geometric_mean_integral_identity.

import Mathlib
open scoped BigOperators Interval

namespace WeightedRootIntegralIdentity

theorem weighted_geometric_mean_cauchy_boundary_integral
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    (∫ x in a 0..a (n - 1),
        (∏ i ∈ Finset.range n, ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ))).im / x) / Real.pi
      = (∑ i ∈ Finset.range n, w i * a i)
          - (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := by sorry

end WeightedRootIntegralIdentity
