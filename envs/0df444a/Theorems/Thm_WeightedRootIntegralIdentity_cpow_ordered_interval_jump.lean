-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_cpow_ordered_interval_jump
-- name    : WeightedRootIntegralIdentity.cpow_ordered_interval_jump
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-13T15:39:59.594513+00:00
-- url     : https://prove2.me/theorems/c10851de-908b-454b-9157-84e238619b2a
-- title:
--   Sine jump across an ordered branch interval
-- statement:
--   Let $a_0\le\cdots\le a_{n-1}$, let $k<n-1$, and suppose $a_k<x<a_{k+1}$. Put
--   $$
--   P(x)=\prod_{i=0}^{n-1}(a_i-x)^{w_i},\qquad
--   M(x)=\prod_{i=0}^{n-1}|a_i-x|^{w_i},
--   $$
--   where complex powers use the principal branch, and let
--   $$
--   \theta_k=\pi\sum_{i=0}^{k}w_i.
--   $$
--   Then the difference between the principal boundary value and its complex conjugate is
--   $$
--   P(x)-\overline{P(x)}=2i\,M(x)\sin\theta_k.
--   $$
--
--   This is the branch-cut jump on the interval $(a_k,a_{k+1})$. After division by $2\pi i$, it produces the sine coefficient in the weighted real-integral identity.
-- source:
--   Boundary-jump calculation in the first answer to https://math.stackexchange.com/questions/4244874/can-we-prove-am-gm-inequality-using-these-integrals, using the intervalwise constant count/weight of negative factors.

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_ordered_interval_boundary
import Theorems.Thm_WeightedRootIntegralIdentity_monotone_on_range_of_adjacent
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem cpow_ordered_interval_jump
    (n k : ℕ) (a w : ℕ → ℝ)
    (hk : k < n - 1)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (x : ℝ) (hxlo : a k < x) (hxhi : x < a (k + 1)) :
    let P : ℂ := ∏ i ∈ Finset.range n, (((a i - x : ℝ) : ℂ) ^ (w i : ℂ))
    let M : ℝ := ∏ i ∈ Finset.range n, Real.rpow |a i - x| (w i)
    let θ : ℝ := Real.pi * (∑ i ∈ Finset.range (k + 1), w i)
    P - star P = ((2 * M * Real.sin θ : ℝ) : ℂ) * Complex.I := by sorry

end WeightedRootIntegralIdentity
