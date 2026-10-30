-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_shape_weierstrass
-- name    : ShapeSOS.ConvexConsistency.shape_weierstrass
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:23:27.64039+00:00
-- url     : https://prove2.me/theorems/5c36d51c-b129-4bdb-a0d3-54f086c64843
-- title:
--   Proposition 3.11 — both shape-constrained uniform approximation assertions
-- statement:
--   Let $B\subset\mathbb R^n$ be a full-dimensional real box, $n\ge1$. Both statements hold:
--
--   1. If $f$ is twice continuously differentiable and convex on $B$, let $g_d$ minimize $\sup_B|f-g|$ over degree-at-most-$d$ polynomials convex on $B$. For every $\epsilon>0$, some $d$ has an attained such minimizer with $\sup_B|g_d-f|<\epsilon$.
--   2. If $f$ is continuously differentiable with $K$-bounded derivatives on $B$, let $h_d$ minimize the same uniform error over degree-at-most-$d$ polynomials with those derivative bounds. For every $\epsilon>0$, some $d$ has an attained such minimizer with $\sup_B|h_d-f|<\epsilon$.
--
--   Equivalently, the relevant best uniform error can be made arbitrarily small in each shape class. Both finite endpoints are permitted in clause (ii), as expressly noted on p. 27. No empirical least-squares objective is used here.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - encoding: smoothness on a closed box → ContDiffOn and coordinate fderivWithin on that box; reason: within-domain derivatives preserve the interior derivatives and their continuous boundary values
--   - encoding: named minimizers of the displayed problems → concrete feasible sets, losses, and attained-minimum relations; reason: optimality compares against every feasible polynomial; it is never replaced by a desired asymptotic property
--   - reading: one-sided standing convention on p. 8, with the two-finite-bound extension expressly stated on p. 27 → clause (ii) permits two finite derivative bounds; reason: the complete approximation result includes the explicitly stated extension
--   - encoding: one of the uniform minimizers g_d or h_d → a deterministic choice together with attained optimality at the degree in the conclusion; reason: all minimizers have the same uniform error, and no zero default can satisfy the conclusion without actual optimality
--   - generalization: Proposition 3.11 describes a smooth function on real n-space → only the required C¹ or C² regularity within the box is imposed; reason: globally smooth source functions specialize to this box-local statement, with the same values and interior derivatives
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 13, Proposition 3.11

import Definitions.Def_ShapeSOS_ConvexConsistency_Estimators

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem shape_weierstrass (n : ℕ) (hn : 0 < n) (B : Box n) :
    (∀ f : Vec n → ℝ, ContDiffOn ℝ 2 f B.carrier → ConvexOn ℝ B.carrier f →
      ∀ ε : ℝ, 0 < ε → ∃ d : ℕ,
        Minimizes (convexClass B d) (approximationLoss B f) (bestConvex B f d) ∧
        uniformError B.carrier (value (bestConvex B f d)) f < ε) ∧
    (∀ (K : DerivativeBounds n) (f : Vec n → ℝ),
      HasBoundedDerivatives B K f → ∀ ε : ℝ, 0 < ε → ∃ d : ℕ,
        Minimizes (derivativeClass B K d) (approximationLoss B f) (bestDerivative B K f d) ∧
        uniformError B.carrier (value (bestDerivative B K f d)) f < ε) := by sorry

end ShapeSOS.ConvexConsistency
