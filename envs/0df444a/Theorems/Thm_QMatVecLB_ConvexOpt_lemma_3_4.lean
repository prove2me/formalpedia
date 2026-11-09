-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_3_4
-- name    : QMatVecLB.ConvexOpt.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:38.658907+00:00
-- url     : https://prove2.me/theorems/76ca6e18-0824-4d09-baaa-f56f4a18a30d
-- title:
--   Lemma 3.4 — Fourier transform of polynomial differentiation
-- statement:
--   Let $b$ be a real-valued Schwartz function on the space of real $n\times n$ matrices, and let $P$ be a polynomial in the matrix coordinates, with complex coefficients. For every matrix $M$,
--
--   $$\widehat{P(\partial_X)b}(M)=P(-2\pi iM)\widehat b(M),\qquad\widehat b(M)=\int e^{2\pi i\langle X,M\rangle}b(X)\,dX.$$
--
--   This identifies differentiation with multiplication for the paper's plus-sign Fourier convention, including the complex polynomial coefficients used in the determinantal witnesses.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: Schwartz functions and polynomial differential operators → Mathlib SchwartzMap with the coordinate sup norm, and a finite monomial sum of iterated coordinate directional derivatives; reason: finite-dimensional Schwartz classes do not depend on the chosen equivalent norm; complex coefficients are needed by the source applications of this lemma
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 3.4, PDF p. 8 (printed p. 7).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Calculus

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_3_4 (n : ℕ) (b : SchwartzMap (RMat n) ℝ)
    (P : MvPolynomial (Fin n × Fin n) ℂ) (M : RMat n) :
    fourierPlus (polynomialDiff P (fun X => (b X : ℂ))) M =
      MvPolynomial.eval (fun ij => -(2 * Real.pi : ℂ) * Complex.I * (M ij.1 ij.2 : ℂ)) P *
        fourierPlus (fun X => (b X : ℂ)) M := by sorry

end QMatVecLB.ConvexOpt
