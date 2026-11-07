-- Prove2me | Theorems.Thm_StatUnlearn_mahalanobis_triangle
-- name    : StatUnlearn.mahalanobis_triangle
-- status  : Proved
-- author  : @2017Advanced@
-- created : 2026-11-06T18:41:46.507915+00:00
-- url     : https://prove2.me/theorems/9df30071-da32-4bd0-8ecc-5e129e4f1138
-- title:
--   Triangle inequality for the Mahalanobis distance
-- statement:
--   For a positive definite covariance $S$ and vectors $x,y$ of $\mathbb{R}^d$, the Mahalanobis distance
--   $$\rho(z)=\Big(\langle z,\,S^{-1}z\rangle\Big)^{1/2}$$
--   satisfies the triangle inequality
--   $$\rho(x+y)\le\rho(x)+\rho(y).$$
--   Equivalently, in the coordinates $z\mapsto S^{-1/2}z$ that make the quadratic form the Euclidean norm, $\rho$ becomes an ordinary norm and this is the triangle inequality for it. It is the single geometric input needed to show that in the feasible region of Proposition 3.1 the removal condition $\alpha\le\rho(\mu_1-\mu)$ is automatic on the preservation ball $\{\mu:\rho(\nu_1-\mu)\le\varepsilon\}$ whenever the levels satisfy $\Delta-\varepsilon\ge\alpha$.
-- source:
--   Pandey, Kulkarni, "Statistical Unlearning of Distributions: A Hypothesis Testing Approach", arXiv:2605.16645, p. 5, proof of Proposition 3.1 (`proof:FFRG`): the Euclidean picture of the region after the change of coordinates x -> Sigma^{-1/2} x

import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
open MeasureTheory

namespace StatUnlearn

theorem mahalanobis_triangle {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosDef)
    (x y : EuclideanSpace ℝ (Fin d)) :
    Real.sqrt (inner ℝ (x + y) (Matrix.toEuclideanLin S⁻¹ (x + y)))
      ≤ Real.sqrt (inner ℝ x (Matrix.toEuclideanLin S⁻¹ x))
        + Real.sqrt (inner ℝ y (Matrix.toEuclideanLin S⁻¹ y)) := by
  sorry

end StatUnlearn
