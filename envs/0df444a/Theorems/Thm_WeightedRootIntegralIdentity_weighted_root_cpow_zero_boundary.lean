-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_cpow_zero_boundary
-- name    : WeightedRootIntegralIdentity.weighted_root_cpow_zero_boundary
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T14:13:57.929456+00:00
-- url     : https://prove2.me/theorems/3d764d66-7701-4e54-9c3a-37f00ef8d017
-- title:
--   Principal weighted root product at the origin
-- statement:
--   Let $a_0,\ldots,a_{n-1}$ be positive real numbers and let real weights $w_i$ satisfy
--   $$
--   \sum_{i=0}^{n-1}w_i=1.
--   $$
--   For the principal complex power, the value of the weighted product at the origin is
--   $$
--   \prod_{i=0}^{n-1}(-a_i)^{w_i}
--   =-\prod_{i=0}^{n-1}a_i^{w_i}.
--   $$
--   Each negative factor contributes the principal phase $e^{\pi i w_i}$; the product of these phases is $e^{\pi i}=-1$. This is the residue-at-zero boundary calculation used in the keyhole-contour proof of the weighted geometric-mean integral representation.
--
--   **Formalization Note** Real powers on the right are represented by `Real.rpow`, while the left uses principal `Complex.cpow`.
-- source:
--   K B Dave, Mathematics Stack Exchange answer to ‘Can we prove AM-GM Inequality using these integrals?’, https://math.stackexchange.com/a/4245016, residue-at-zero calculation displayed after the Laurent expansions; weighted analogue from Feng Qi, Xiao-Jing Zhang, and Wen-Hui Li, Acta Mathematica Sinica 30 (2014), Theorem 3.1.

import Theorems.Thm_WeightedRootIntegralIdentity_cpow_finset_boundary_product
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_cpow_zero_boundary
    (n : ℕ) (a w : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hwsum : (∑ i ∈ Finset.range n, w i) = 1) :
    (∏ i ∈ Finset.range n,
        (((0 : ℂ) - (a i : ℂ)) ^ (w i : ℂ))) =
      -((∏ i ∈ Finset.range n, Real.rpow (a i) (w i) : ℝ) : ℂ) := by sorry

end WeightedRootIntegralIdentity
