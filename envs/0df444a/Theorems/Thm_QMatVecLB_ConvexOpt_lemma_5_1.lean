-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_5_1
-- name    : QMatVecLB.ConvexOpt.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:33.675055+00:00
-- url     : https://prove2.me/theorems/f43df1e0-9087-4f62-bb20-392d3be4d421
-- title:
--   Lemma 5.1 — Cayley operator on a Gaussian kernel
-- statement:
--   For every real $n\times n$ matrix $X$, let $\langle X,X\rangle=\sum_{ij}X_{ij}^2$. The Cayley operator satisfies
--
--   $$\det(\partial_X)e^{-\langle X,X\rangle/2}=(-1)^n\det(X)e^{-\langle X,X\rangle/2}.$$
--
--   This is a pointwise identity in every dimension, including the empty determinant convention. It describes the first application of the determinant differential operator to the unnormalized Gaussian kernel.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 5.1, PDF p. 12 (printed p. 11).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Calculus

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_5_1 (n : ℕ) (X : RMat n) :
    cayley gaussianKernel X = (-1 : ℝ)^n * X.det * gaussianKernel X := by sorry

end QMatVecLB.ConvexOpt
