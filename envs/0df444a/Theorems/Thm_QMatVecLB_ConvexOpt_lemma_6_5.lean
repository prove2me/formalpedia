-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_6_5
-- name    : QMatVecLB.ConvexOpt.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:21.846868+00:00
-- url     : https://prove2.me/theorems/d883d9f8-2ffa-4c6c-94d7-3c98407378e7
-- title:
--   Lemma 6.5 — Gaussian singular values and vector norm bounds
-- statement:
--   Let $n\ge1$, let $B$ have independent standard normal entries, and let $v$ be a standard Gaussian vector with its Euclidean norm. The spectral-norm square and smallest singular value are integrable, and
--
--   $$\Pr[\sigma_{\max}(B)>3\sqrt n]\le e^{-n/2},\qquad\mathbb E[\sigma_{\max}(B)^2]\le12n,$$
--   $$\mathbb E[\sigma_{\min}(B)]\ge\frac1{2\sqrt n},\qquad\Pr[\|v\|_2^2\notin[n/2,2n]]\le2e^{-n/16}.$$
--
--   All four bounds are asserted together. The cited random-matrix and chi-square results are proof ingredients, rather than hypotheses of this lemma.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: expectations and witness integrals → the same integrals, with their integrability also asserted in the conclusion; reason: the source uses convergent integrals; convergence is made explicit rather than relying on the totalized nonintegrable Bochner integral
--   - encoding: positive dimension and Euclidean Gaussian vector norm → 1 <= n and the norm of EuclideanSpace R (Fin n); reason: the square-root denominators and singular-value bounds use positive dimension; this prevents substituting the coordinate sup norm
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 6.5, PDF p. 21 (printed p. 20).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Inversion

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_6_5 (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun B : RMat n => GaussianMatrix.specNorm B ^ 2)
      (GaussianMatrix.gaussianMatrix n n) ∧
    Integrable (fun B : RMat n => GaussianMatrix.sMin B) (GaussianMatrix.gaussianMatrix n n) ∧
    ((GaussianMatrix.gaussianMatrix n n) {B | 3 * Real.sqrt n < GaussianMatrix.specNorm B}).toReal ≤
      Real.exp (-(n : ℝ) / 2) ∧
    (∫ B : RMat n, GaussianMatrix.specNorm B ^ 2 ∂GaussianMatrix.gaussianMatrix n n) ≤ 12 * (n : ℝ) ∧
    1 / (2 * Real.sqrt n) ≤ (∫ B : RMat n, GaussianMatrix.sMin B ∂GaussianMatrix.gaussianMatrix n n) ∧
    ((standardVector n) {v | ‖vectorEuclidean v‖ ^ 2 ∉ Set.Icc ((n : ℝ)/2) (2*(n : ℝ))}).toReal ≤
      2 * Real.exp (-(n : ℝ) / 16) := by sorry

end QMatVecLB.ConvexOpt
