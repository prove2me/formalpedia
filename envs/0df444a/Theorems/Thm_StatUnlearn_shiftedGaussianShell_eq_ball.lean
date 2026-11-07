-- Prove2me | Theorems.Thm_StatUnlearn_shiftedGaussianShell_eq_ball
-- name    : StatUnlearn.shiftedGaussianShell_eq_ball
-- status  : Proved
-- author  : @2017Advanced@
-- created : 2026-11-06T18:03:42.42411+00:00
-- url     : https://prove2.me/theorems/2f66905d-22a6-46f0-8983-8d036e4f7beb
-- title:
--   The Mahalanobis shell is the whole ball when the levels separate
-- statement:
--   For shifted Gaussians on $\mathbb{R}^d$ with common positive definite covariance $S$ and levels $\alpha,\varepsilon\ge0$, if
--   $$\Delta-\varepsilon\ge\alpha,\qquad \Delta=\big(\langle\mu_1-\nu_1,S^{-1}(\mu_1-\nu_1)\rangle\big)^{1/2},$$
--   then the removal condition $\alpha\le\big(\langle\mu_1-\mu,S^{-1}(\mu_1-\mu)\rangle\big)^{1/2}$ holds automatically on the whole preservation ball, so the shell equals that ball:
--   $$\Big\{\mu:\ \alpha\le \big(\langle\mu_1-\mu,S^{-1}(\mu_1-\mu)\rangle\big)^{1/2},\ \big(\langle\nu_1-\mu,S^{-1}(\nu_1-\mu)\rangle\big)^{1/2}\le\varepsilon\Big\}=\Big\{\mu:\ \big(\langle\nu_1-\mu,S^{-1}(\nu_1-\mu)\rangle\big)^{1/2}\le\varepsilon\Big\}.$$
--   This is the "whole ball" clause of Proposition 3.1, with the ball in the Mahalanobis metric induced by $S^{-1}$; for $S=1$ it is the Euclidean closed ball $\bar B(\nu_1,\varepsilon)$ of the paper.
-- source:
--   Pandey, Kulkarni, "Statistical Unlearning of Distributions: A Hypothesis Testing Approach", arXiv:2605.16645, p. 5, Proposition 3.1 (`thm:FFR`), whole-ball case

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
open MeasureTheory ProbabilityTheory

namespace StatUnlearn

theorem shiftedGaussianShell_eq_ball {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (μ₁ ν₁ : EuclideanSpace ℝ (Fin d)) (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (h : Real.sqrt (inner ℝ (μ₁ - ν₁) (Matrix.toEuclideanLin S⁻¹ (μ₁ - ν₁))) - ε ≥ α) :
    ({μ : EuclideanSpace ℝ (Fin d) |
        α ≤ Real.sqrt (inner ℝ (μ₁ - μ) (Matrix.toEuclideanLin S⁻¹ (μ₁ - μ))) ∧
        Real.sqrt (inner ℝ (ν₁ - μ) (Matrix.toEuclideanLin S⁻¹ (ν₁ - μ))) ≤ ε}
      : Set (EuclideanSpace ℝ (Fin d)))
      = ({μ : EuclideanSpace ℝ (Fin d) |
        Real.sqrt (inner ℝ (ν₁ - μ) (Matrix.toEuclideanLin S⁻¹ (ν₁ - μ))) ≤ ε}
      : Set (EuclideanSpace ℝ (Fin d))) := by
  sorry

end StatUnlearn
