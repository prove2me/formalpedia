-- Prove2me | Theorems.Thm_Verlinde2016_hessian_sq_integral_eq_laplacian_sq
-- name    : Verlinde2016.hessian_sq_integral_eq_laplacian_sq
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T22:32:18.342223+00:00
-- url     : https://prove2.me/theorems/579e140a-19f4-46a7-9a8c-7b233991ed9f
-- title:
--   Eq. (7.31) — $\int(\nabla_i\nabla_j\chi)^2 = \int(\nabla^2\chi)^2$
-- statement:
--   For a function $\chi$ on $n$-dimensional Euclidean space that falls off fast enough that no boundary terms arise, a double integration by parts gives (summation over $i,j$)
--   $$\int (\nabla_i\nabla_j\chi)^2\,dV = \int (\nabla^2\chi)^2\,dV .$$
--   Formalization: "falls off rapidly enough" is taken as $\chi$ being $C^\infty$ with compact support, a sufficient condition for the absence of boundary terms.
-- source:
--   E. Verlinde, Emergent Gravity and the Dark Universe, SciPost Phys. 2, 016 (2017), arXiv:1611.02269v2, https://arxiv.org/abs/1611.02269, p. 35, eq. (7.31)

import Mathlib
import Definitions.Def_Verlinde2016_Defs

open Real

namespace Verlinde2016

theorem hessian_sq_integral_eq_laplacian_sq {n : ℕ} (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ_supp : HasCompactSupport χ) :
    ∑ i, ∑ j, ∫ x, partialDeriv i (partialDeriv j χ) x ^ 2
      = ∫ x, (∑ i, partialDeriv i (partialDeriv i χ) x) ^ 2 := by sorry

end Verlinde2016
