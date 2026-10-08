-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_reciprocal_deriv_at_zero
-- name    : WeightedRootIntegralIdentity.weighted_root_reciprocal_deriv_at_zero
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T14:27:08.640975+00:00
-- url     : https://prove2.me/theorems/90042285-6347-49f8-8e29-1696d4d746eb
-- title:
--   First-order coefficient of the weighted root product at infinity
-- statement:
--   Let $a_0,\ldots,a_{n-1}$ and $w_0,\ldots,w_{n-1}$ be real numbers. Define, near the origin,
--   $$
--   G(u)=\prod_{i=0}^{n-1}(1-a_i u)^{w_i},
--   $$
--   where each power is the principal complex power. Then
--   $$
--   G'(0)=-\sum_{i=0}^{n-1}w_i a_i.
--   $$
--   Under the reciprocal substitution $u=1/z$, this derivative is the first-order coefficient in the expansion of the weighted root product at infinity. It supplies the arithmetic-mean term in the keyhole-contour calculation.
--
--   **Formalization Note** The derivative is a complex derivative; the real weighted sum is coerced to $\mathbb C$.
-- source:
--   K B Dave, Mathematics Stack Exchange answer to ‘Can we prove AM-GM Inequality using these integrals?’, https://math.stackexchange.com/a/4245016, Laurent expansion at infinity displayed before the residue evaluations; weighted analogue from Feng Qi, Xiao-Jing Zhang, and Wen-Hui Li, Acta Mathematica Sinica 30 (2014), Theorem 3.1.

import Mathlib
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_reciprocal_deriv_at_zero
    (n : ℕ) (a w : ℕ → ℝ) :
    HasDerivAt
      (fun z : ℂ =>
        ∏ i ∈ Finset.range n, (1 - (a i : ℂ) * z) ^ (w i : ℂ))
      (-((∑ i ∈ Finset.range n, w i * a i : ℝ) : ℂ)) 0 := by sorry

end WeightedRootIntegralIdentity
