-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_5_3
-- name    : QMatVecLB.ConvexOpt.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:54.846344+00:00
-- url     : https://prove2.me/theorems/0dcaf21e-993f-4e7f-ae79-7e91b9926bfc
-- title:
--   Lemma 5.3 — Cayley's identity
-- statement:
--   For every dimension $n$ and natural exponent $z$, the following is an identity of polynomials in the entries of an $n\times n$ matrix $X$:
--
--   $$\det(\partial_X)(\det X)^z=\left(\prod_{j=0}^{n-1}(z+j)\right)(\det X)^{z-1}.$$
--
--   The empty product and determinant are one. For $z=0$ and $n>0$, the rising factorial vanishes. This identity supplies the determinant moments used by the Gaussian witness calculations.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: matrix of variables, rising factorial and exponent z-1 → an identity in MvPolynomial over the real numbers, the finite rising product, and natural subtraction z-1; reason: for z=0 and n>0 the coefficient is zero, and for n=0 the determinant is one; the totalized exponent therefore preserves every case
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 5.3, PDF p. 13 (printed p. 12).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Calculus

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_5_3 (n z : ℕ) :
    polynomialCayley (detPolynomial n ^ z) =
      MvPolynomial.C (rising z n) * detPolynomial n ^ (z-1) := by sorry

end QMatVecLB.ConvexOpt
