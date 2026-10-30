-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_sos_convex_perturbation
-- name    : ShapeSOS.ConvexConsistency.sos_convex_perturbation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:22:48.185872+00:00
-- url     : https://prove2.me/theorems/8366464c-d33a-41c6-b5c9-69296812bcbf
-- title:
--   Theorem 3.1 — the printed Theta perturbation eventually makes a polynomial SOS-convex
-- statement:
--   Let $n\ge1$ and let $g$ be a real polynomial convex on $[-1,1]^n$. For each $d\in\mathbb N$, define
--   $$\Theta_d(x)=\sum_i x_i^2+\sum_{i<j}(8x_i^{2d+2}+x_i^{2d}x_j^2+x_i^2x_j^{2d}+8x_j^{2d+2}).$$
--   For every $\epsilon>0$, the source asserts
--   $$\exists d_0\ \forall d\ge d_0,\qquad g+\epsilon\Theta_d\text{ is SOS-convex}.$$
--   SOS-convexity means the actual Hessian admits a polynomial factorization $V^TV$. The premise requires convexity only on the cube. The printed one-dimensional case is retained and documented as false in I3.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 8, Theorem 3.1

import Definitions.Def_ShapeSOS_ConvexConsistency_Algebra

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem sos_convex_perturbation (n : ℕ) (hn : 0 < n) (g : Poly n)
    (hg : ConvexOn ℝ (cube n (-1) 1) (value g)) (ε : ℝ) (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, RobustPMI.Hierarchy.IsSOSConvex
      (g + MvPolynomial.C ε * theta n d) := by sorry

end ShapeSOS.ConvexConsistency
