-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_complex_boundary_jump
-- name    : WeightedRootIntegralIdentity.weighted_root_complex_boundary_jump
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-13T18:56:01.015827+00:00
-- url     : https://prove2.me/theorems/ffe62e14-2fb3-4321-aa03-6337820c7800
-- title:
--   Boundary value of $\prod_i (x-a_i)^{w_i}$ on the gap $(a_k,a_{k+1})$
-- statement:
--   Let $n\ge 2$, let $a_0\le a_1\le\cdots\le a_{n-1}$ be real numbers, and let $w_0,\ldots,w_{n-1}$ be real weights with $\sum_{i=0}^{n-1}w_i=1$. For a complex number $z$ and a real exponent $w$, let $z^{w}$ denote the principal power $\exp(w\operatorname{Log} z)$, whose branch cut is the negative real axis and which assigns argument $\pi$ to a negative real base.
--
--   Fix an index $k$ with $0\le k\le n-2$ and a real point $x$ strictly inside the gap, $a_k<x<a_{k+1}$. Then
--
--   $$\operatorname{Im}\prod_{i=0}^{n-1}(x-a_i)^{w_i}
--   =\sin\!\Big(\pi\sum_{i=0}^{k}w_i\Big)\prod_{i=0}^{n-1}|x-a_i|^{w_i}.$$
--
--   In other words, the principal branch of $\prod_i(z-a_i)^{w_i}$, evaluated on the real segment $(a_k,a_{k+1})$, is the upper boundary value of the analytic continuation from the upper half plane: the factors with $i\le k$ have positive base and are real, while each factor with $i\ge k+1$ has negative base and contributes a phase $e^{i\pi w_i}$. The total phase is therefore $\pi\sum_{i>k}w_i=\pi\big(1-\sum_{i\le k}w_i\big)$, and $\sin\big(\pi(1-\sum_{i\le k}w_i)\big)=\sin\big(\pi\sum_{i\le k}w_i\big)$ gives the stated formula. This is the jump of the multivalued function $\prod_i(z-a_i)^{w_i}$ across its cut.
-- source:
--   Feng Qi, Xiao-Jing Zhang, and Wen-Hui Li, An integral representation for the weighted geometric mean and its applications, Acta Mathematica Sinica (English Series) 30 (2014), Theorem 3.1 (case z = 0); the identity is summarized as equation (4) at https://math.stackexchange.com/questions/4244874/can-we-prove-am-gm-inequality-using-these-integrals . This statement is one of the two steps of the standard contour-integral proof of that theorem, introduced here as a lemma in the decomposition of WeightedRootIntegralIdentity.weighted_geometric_mean_integral_identity.

import Mathlib
open scoped BigOperators Interval

namespace WeightedRootIntegralIdentity

theorem weighted_root_complex_boundary_jump
    (n : ℕ) (a w : ℕ → ℝ)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1)
    (k : ℕ) (hk : k < n - 1) (x : ℝ) (hxl : a k < x) (hxr : x < a (k + 1)) :
    (∏ i ∈ Finset.range n, ((x : ℂ) - (a i : ℂ)) ^ ((w i : ℂ))).im
      = Real.sin (Real.pi * (∑ i ∈ Finset.range (k + 1), w i)) *
          ∏ i ∈ Finset.range n, Real.rpow |x - a i| (w i) := by sorry

end WeightedRootIntegralIdentity
