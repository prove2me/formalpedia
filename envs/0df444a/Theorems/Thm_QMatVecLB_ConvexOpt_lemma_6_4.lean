-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_6_4
-- name    : QMatVecLB.ConvexOpt.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:50.54335+00:00
-- url     : https://prove2.me/theorems/1cf9fdc4-f3e4-4947-8a60-a9031ba6dccd
-- title:
--   Lemma 6.4 — scalar form and positivity of the correlation
-- statement:
--   Let $n\ge1$, $\theta>0$, $\Psi_\theta(x)=\Phi(x+1/\theta)-\Phi(x-1/\theta)$ and $g_\theta(x)=-x\Psi'_\theta(x)$, where $\Phi$ is the standard normal cumulative distribution function. Let $P_\theta(B)$ be the probability over independent standard normal border variables that the upper-left entry of the inverse bordered matrix has magnitude at least $\theta$, set to zero when $B$ is singular. Then
--
--   $$\mathbb E[q(B)P_\theta(B)]=(n-1)!\mathbb E_{u,v,B}[g_\theta(u^TB^{-1}v)]\ge0.$$
--
--   The displayed integrands are integrable. All entries of $u,v,B$ are independent standard normals. The result identifies the witness correlation with a nonnegative scalar expectation.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: positive matrix dimension in the inversion section → 1 <= n; reason: the inversion section concerns a nonempty interior block; at n=0 the factorial formula of Lemma 6.3 is not valid
--   - encoding: expectations and witness integrals → the same integrals, with their integrability also asserted in the conclusion; reason: the source uses convergent integrals; convergence is made explicit rather than relying on the totalized nonintegrable Bochner integral
--   - encoding: theta in Psi_theta and the inverse threshold → 0 < theta; reason: this is the nondegenerate positive-threshold domain used in (120) and (122)
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 6.4, PDF p. 20 (printed p. 19).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Inversion

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_6_4 (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun B : RMat n => q B * borderProbability θ B)
      (GaussianMatrix.gaussianMatrix n n) ∧
    Integrable (scalarIntegrand (n := n) θ) (scalarLaw n) ∧
    (∫ B : RMat n, q B * borderProbability θ B ∂GaussianMatrix.gaussianMatrix n n) =
      ((n-1).factorial : ℝ) * ∫ uvB, scalarIntegrand θ uvB ∂scalarLaw n ∧
    0 ≤ (∫ B : RMat n, q B * borderProbability θ B ∂GaussianMatrix.gaussianMatrix n n) := by sorry

end QMatVecLB.ConvexOpt
