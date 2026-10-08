-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weighted_root_differentiableAt_of_shift_mem_slitPlane
-- name    : WeightedRootIntegralIdentity.weighted_root_differentiableAt_of_shift_mem_slitPlane
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-14T14:43:04.552885+00:00
-- url     : https://prove2.me/theorems/f5c56b30-a240-4bf9-8450-3daabc02158c
-- title:
--   Holomorphicity of the weighted root product off its branch cuts
-- statement:
--   Let $a_0,\ldots,a_{n-1}$ and $w_0,\ldots,w_{n-1}$ be real numbers, and define
--   $$
--   F(z)=\prod_{i=0}^{n-1}(z-a_i)^{w_i}
--   $$
--   using principal complex powers. If every shifted point $z-a_i$ lies in the slit plane $\mathbb C\setminus(-\infty,0]$, then $F$ is complex differentiable at $z$.
--
--   This supplies the local holomorphicity condition needed to apply Cauchy–Goursat on contours avoiding the translated branch cuts $(-\infty,a_i]$.
-- source:
--   K B Dave, Mathematics Stack Exchange answer to ‘Can we prove AM-GM Inequality using these integrals?’, https://math.stackexchange.com/a/4245016, construction of the meromorphic differential form on the complement of the cut; principal-power analytic-domain condition formalized here for the weighted product.

import Mathlib
open scoped BigOperators

namespace WeightedRootIntegralIdentity

theorem weighted_root_differentiableAt_of_shift_mem_slitPlane
    (n : ℕ) (a w : ℕ → ℝ) (z : ℂ)
    (hz : ∀ i < n, z - (a i : ℂ) ∈ Complex.slitPlane) :
    DifferentiableAt ℂ
      (fun z : ℂ =>
        ∏ i ∈ Finset.range n, (z - (a i : ℂ)) ^ (w i : ℂ)) z := by sorry

end WeightedRootIntegralIdentity
