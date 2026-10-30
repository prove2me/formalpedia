-- Prove2me | Theorems.Thm_ShapeSOS_ConvexConsistency_matrix_sos_approximation
-- name    : ShapeSOS.ConvexConsistency.matrix_sos_approximation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:22:52.584239+00:00
-- url     : https://prove2.me/theorems/25084ff2-6374-48aa-bf53-4e7e78c9b7ee
-- title:
--   Lemma 3.7 — SOS approximation of a PSD polynomial matrix quadratic form
-- statement:
--   Let $n\ge1$ and let $M(x)$ be an $n\times n$ real polynomial matrix that is positive semidefinite for every $x\in[-1,1]^n$. Put $\Phi_d(x,y)=\sum_i y_i^2(1+\sum_j x_j^{2d})$. For every $\epsilon>0$,
--   $$\exists d_0\ \forall d\ge d_0,\qquad y^TM(x)y+\epsilon\Phi_d(x,y)\text{ is a sum of polynomial squares in }(x,y).$$
--   The SOS certificate is joint in $x$ and $y$, with unrestricted finite square count. This is the matrix perturbation support for Theorem 3.1.
--
--   Differences from the source:
--   - encoding: real finite-dimensional coordinates and Euclidean geometry → Fin n → ℝ with its usual topology and explicit norm₂ = sqrt(sum x_i²); reason: the topology is the Euclidean topology and all numerical distances use the Euclidean norm
--   - reading: let y belong to real n-space and the expression is SOS → one joint polynomial in independent x and y variables; reason: p. 3 defines SOS matrices through a joint polynomial, and the use on p. 12 requires this reading
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 11, Lemma 3.7

import Definitions.Def_ShapeSOS_ConvexConsistency_Algebra

set_option autoImplicit false
open Filter MeasureTheory
open scoped BigOperators Topology MeasureTheory

namespace ShapeSOS.ConvexConsistency

theorem matrix_sos_approximation (n : ℕ) (hn : 0 < n) (M : PMat n)
    (hM : ∀ x ∈ cube n (-1) 1, (M.map (MvPolynomial.eval x)).PosSemidef)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, RobustPMI.Hierarchy.IsSOSPoly
      (jointQuadratic M + MvPolynomial.C ε * phi n d) := by sorry

end ShapeSOS.ConvexConsistency
