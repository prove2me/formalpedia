-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_geometric_mean_integral_identity
-- name    : WeightedRootIntegralIdentity.weighted_geometric_mean_integral_identity
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-13T14:27:35.95713+00:00
-- url     : https://prove2.me/theorems/347e12ae-a6b5-4d3e-8643-a18a32defe3a
-- title:
--   Weighted geometric-mean integral identity
-- statement:
--   Let $n\ge 2$. Let $0<a_0\le\cdots\le a_{n-1}$ and let $w_0,\ldots,w_{n-1}>0$ satisfy $\sum_i w_i=1$. Then
--
--   $$
--   \sum_{k=0}^{n-2}\frac{\sin(\pi\sum_{i=0}^k w_i)}{\pi}
--   \int_{a_k}^{a_{k+1}}\frac{\prod_{i=0}^{n-1}|x-a_i|^{w_i}}{x}\,dx
--   =\sum_{i=0}^{n-1}w_i a_i-\prod_{i=0}^{n-1}a_i^{w_i}.
--   $$
--
--   This is the zero-shift weighted geometric-mean integral representation. Equal weights $w_i=1/n$ recover the root-integral identity.
-- source:
--   Feng Qi, Xiao-Jing Zhang, and Wen-Hui Li, An integral representation for the weighted geometric mean and its applications, Acta Mathematica Sinica 30 (2014), Theorem 3.1 at z = 0; summarized as equation (4) at https://math.stackexchange.com/questions/4244874/can-we-prove-am-gm-inequality-using-these-integrals

import Mathlib
open scoped BigOperators Interval

namespace WeightedRootIntegralIdentity

theorem weighted_geometric_mean_integral_identity
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    (∑ k ∈ Finset.range (n - 1),
      (Real.sin (Real.pi * (∑ i ∈ Finset.range (k + 1), w i)) / Real.pi) *
        ∫ x in a k..a (k + 1),
          (∏ i ∈ Finset.range n, Real.rpow |x - a i| (w i)) / x)
      = (∑ i ∈ Finset.range n, w i * a i)
          - (∏ i ∈ Finset.range n, Real.rpow (a i) (w i)) := by sorry

end WeightedRootIntegralIdentity
