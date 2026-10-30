-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_hessian_perturbation
-- name    : ShapeSOS.ConvexConsistency.hessian_perturbation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:22:54.353375+00:00
-- url     : https://prove2.me/theorems/83f1f05f-56d7-4294-9a5c-d32fc095b554
-- title:
--   Proposition 3.4 — the exact Theta Hessian residual is SOS
-- statement:
--   Let $n\ge1$ and let $\Theta_d$ be exactly the polynomial of Theorem 3.1. For every integer $d\ge1$, the source asserts
--   $$y^TH_{\Theta_d}(x)y-\sum_i y_i^2(1+\sum_jx_j^{2d})\text{ is SOS in }(x,y).$$
--   The Hessian uses actual second partial derivatives. No dimension is dropped; the failure at $n=1$ is recorded in I3 alongside the failure of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - reading: the swapped subscript and prime in H_{Theta′_d} → the Hessian of the already defined Theta_dprime; reason: the reference to Theorem 3.1 identifies the polynomial unambiguously
--   - reading: the expression in x and a vector y is SOS → SOS in the joint variables x,y; reason: the source SOS-matrix definition and its subsequent use require a single joint certificate
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 9, Proposition 3.4

import Definitions.Def_ShapeSOS_ConvexConsistency_Algebra

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem hessian_perturbation (n : ℕ) (hn : 0 < n) (d : ℕ) (hd : 1 ≤ d) :
    RobustPMI.Hierarchy.IsSOSPoly
      (jointQuadratic (RobustPMI.Hierarchy.hessian (theta n d)) - phi n d) := by sorry

end ShapeSOS.ConvexConsistency
