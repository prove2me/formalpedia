-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_5_4
-- name    : QMatVecLB.ConvexOpt.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:59.793777+00:00
-- url     : https://prove2.me/theorems/3df529de-b9fe-4e79-ad5e-8467d9390d7c
-- title:
--   Lemma 5.4 — two Gaussian moments of q
-- statement:
--   Let $A$ have independent standard normal entries and define
--
--   $$q(X)=e^{\langle X,X\rangle/2}\det(\partial_X)^2e^{-\langle X,X\rangle/2}.$$
--
--   Both integrands below are integrable, and for every dimension $n$,
--
--   $$\mathbb E[q(A)^2]=\mathbb E[q(A)(\det A)^2]=(n+1)!n!.$$
--
--   The differential definition of $q$ is retained rather than replacing it with a formula obtained during the proof. The identities normalize the squared determinantal witness.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: expectations and witness integrals → the same integrals, with their integrability also asserted in the conclusion; reason: the source uses convergent integrals; convergence is made explicit rather than relying on the totalized nonintegrable Bochner integral
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 5.4, PDF p. 13 (printed p. 12).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Inversion

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_5_4 (n : ℕ) :
    Integrable (fun A : RMat n => q A ^ 2) (GaussianMatrix.gaussianMatrix n n) ∧
    Integrable (fun A : RMat n => q A * A.det ^ 2) (GaussianMatrix.gaussianMatrix n n) ∧
    (∫ A : RMat n, q A ^ 2 ∂GaussianMatrix.gaussianMatrix n n) =
      (∫ A : RMat n, q A * A.det ^ 2 ∂GaussianMatrix.gaussianMatrix n n) ∧
    (∫ A : RMat n, q A * A.det ^ 2 ∂GaussianMatrix.gaussianMatrix n n) =
      ((n+1).factorial : ℝ) * (n.factorial : ℝ) := by sorry

end QMatVecLB.ConvexOpt
