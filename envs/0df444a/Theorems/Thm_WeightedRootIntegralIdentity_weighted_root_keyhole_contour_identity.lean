-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_keyhole_contour_identity
-- name    : WeightedRootIntegralIdentity.weighted_root_keyhole_contour_identity
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T14:33:24.294261+00:00
-- url     : https://prove2.me/theorems/c586af72-bb39-45fc-8e58-83d6855c2ea8
-- title:
--   Keyhole-contour identity for a weighted root product
-- statement:
--   Let $n\ge2$, let $0<a_0\le\cdots\le a_{n-1}$, and let positive weights $w_i$ sum to one. Put
--   $$
--   F(z)=\prod_{i=0}^{n-1}(z-a_i)^{w_i},
--   \qquad
--   G(u)=\prod_{i=0}^{n-1}(1-a_i u)^{w_i},
--   $$
--   using principal complex powers. Then the jump integral along the slit satisfies
--   $$
--   \frac1\pi\int_{a_0}^{a_{n-1}}\frac{\operatorname{Im}F(x)}{x}\,dx
--   =-\operatorname{Re}G'(0)+\operatorname{Re}F(0).
--   $$
--   This is the pure keyhole-contour step: Cauchy–Goursat identifies the integral along the two banks of the slit with the local contribution at the origin and the first-order coefficient in the reciprocal coordinate at infinity. It deliberately leaves those two local coefficients unevaluated, so their algebraic evaluations can be reused independently.
--
--   **Formalization Note** The contour coefficient at infinity is represented by `Complex.deriv G 0`; the origin contribution is the real part of the finite principal-power product at zero.
-- source:
--   K B Dave, Mathematics Stack Exchange answer to ‘Can we prove AM-GM Inequality using these integrals?’, https://math.stackexchange.com/a/4245016, contour comparison and Laurent expansions in the displayed equations preceding the boxed identity; weighted version: Feng Qi, Xiao-Jing Zhang, and Wen-Hui Li, An integral representation for the weighted geometric mean and its applications, Acta Mathematica Sinica (English Series) 30 (2014), Theorem 3.1.

import Mathlib
open scoped BigOperators Interval

namespace WeightedRootIntegralIdentity

theorem weighted_root_keyhole_contour_identity
    (n : ℕ) (hn : 2 ≤ n) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hwpos : ∀ i < n, 0 < w i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    (∫ x in a 0..a (n - 1),
        (∏ i ∈ Finset.range n,
          ((x : ℂ) - (a i : ℂ)) ^ (w i : ℂ)).im / x) / Real.pi =
      -(deriv
          (fun u : ℂ =>
            ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * u) ^ (w i : ℂ)) 0).re +
        (∏ i ∈ Finset.range n,
          (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))).re := by sorry

end WeightedRootIntegralIdentity
