-- Prove2me | Theorems.Thm_RobustOpt2009_MatrixChance_gaussian_smooth_approximation
-- name    : RobustOpt2009.MatrixChance.gaussian_smooth_approximation
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-22T21:10:43.36208+00:00
-- url     : https://prove2.me/theorems/4665bb04-8fea-4f74-bc3b-f8f1c3d258e7
-- title:
--   Gaussian smoothing of bounded Lipschitz functions
-- statement:
--   A bounded 1-Lipschitz function on finite-dimensional Euclidean space with values in $[0,R]$ admits uniformly close smooth approximations with values in the same interval. For any positive error tolerance, the approximation has gradient of norm at most one, uniformly bounded symmetric Hessian, and continuous uniformly bounded third derivative. This approximation lets smooth Gaussian functional inequalities be applied to truncated distance functions.
-- source:
--   Auxiliary Gaussian smoothing lemma for the enlargement inequality in Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization (2009), Appendix B.5.1, proof of Theorem B.5.1, fact (!), pp. 508–509. https://doi.org/10.1515/9781400831050

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators RealInnerProductSpace NNReal ENNReal

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

theorem RobustOpt2009.MatrixChance.gaussian_smooth_approximation {d : E → ℝ} (hdc : Continuous d) {R : ℝ} (hR : 0 ≤ R)
    (hd_mem : ∀ x, d x ∈ Icc 0 R) (hd_lip : ∀ x y, |d x - d y| ≤ ‖x - y‖)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (F : E → ℝ) (g : E → E) (K : E → (E →L[ℝ] E)) (M : E → (E →L[ℝ] (E →L[ℝ] E)))
      (CK CM : ℝ),
      (∀ x, F x ∈ Icc 0 R) ∧
      (∀ x, |F x - d x| ≤ δ) ∧
      (∀ x, HasFDerivAt F (innerSL ℝ (g x)) x) ∧
      (∀ x, HasFDerivAt g (K x) x) ∧
      (∀ x, HasFDerivAt K (M x) x) ∧
      Continuous M ∧
      (∀ x v w, ⟪K x v, w⟫ = ⟪v, K x w⟫) ∧
      (∀ x, ‖g x‖ ≤ 1) ∧
      (∀ x, ‖K x‖ ≤ CK) ∧
      (∀ x, ‖M x‖ ≤ CM) := by sorry
