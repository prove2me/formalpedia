-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_lemma_6_1
-- name    : QMatVecLB.ConvexOpt.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:23.796754+00:00
-- url     : https://prove2.me/theorems/f8296712-5d0c-4460-aee2-54f4b3099a2b
-- title:
--   Lemma 6.1 — determinantal witness correlation
-- statement:
--   Fix $\theta\ge5$. There are $c_\theta>0$ and a dimension threshold $N$ such that for all $n\ge N$,
--
--   $$\left|\int D_\theta(A)\,d\beta_I^{(2)}(A)\right|=\frac{\left|\mathbb E[q(B)P_\theta(B)]\right|}{(2\pi)^{2n}}\ge\frac{c_\theta}{(2\pi)^{2n}}\frac{(n-1)!}{n}.$$
--
--   Here $A$ is $(n+1)\times(n+1)$, $I$ indexes the interior $n\times n$ block, $D_\theta$ is the inverse-entry decision function, and the witness density is the squared scaled minor Cayley operator applied to the standard Gaussian density. Both integrals are asserted integrable. This is the quantitative correlation needed for the inversion lower bound.
--
--   Differences from the source:
--   - encoding: real n by n matrices and their coordinate indices → RMat n with indices Fin n, the coordinate product measurable space and product Lebesgue measure; reason: this is the same finite-dimensional real matrix space; changing the index origin changes no instance
--   - encoding: expectations and witness integrals → the same integrals, with their integrability also asserted in the conclusion; reason: the source uses convergent integrals; convergence is made explicit rather than relying on the totalized nonintegrable Bochner integral
--   - encoding: the measure beta_I^(2) and border indices 1 and {2,...,n+1} → the complex density betaBorder against product Lebesgue measure, border index 0 and interior embedding Fin.succ; reason: a density specifies the same complex measure; shifting all indices preserves the inverse entry and minor; both absolute values in (93) are retained
--   - encoding: all sufficiently large n → an existential threshold N>=2; reason: this is the same eventual statement, with denominators and factorials confined to positive dimension
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 6.1, PDF p. 17 (printed p. 16).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Inversion

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt
attribute [local instance] Classical.propDecidable

theorem lemma_6_1 (θ : ℝ) (hθ : 5 ≤ θ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      Integrable (fun A : RMat (n+1) => (inverseDecision θ A : ℂ) * betaBorder n A)
        (matrixLebesgue (n+1)) ∧
      Integrable (fun B : RMat n => q B * borderProbability θ B)
        (GaussianMatrix.gaussianMatrix n n) ∧
      ‖∫ A : RMat (n+1), (inverseDecision θ A : ℂ) * betaBorder n A ∂matrixLebesgue (n+1)‖ =
        |∫ B : RMat n, q B * borderProbability θ B ∂GaussianMatrix.gaussianMatrix n n| /
          (2 * Real.pi) ^ (2*n) ∧
      (c / (2 * Real.pi) ^ (2*n)) * (((n-1).factorial : ℝ) / (n : ℝ)) ≤
        |∫ B : RMat n, q B * borderProbability θ B ∂GaussianMatrix.gaussianMatrix n n| /
          (2 * Real.pi) ^ (2*n) := by sorry

end QMatVecLB.ConvexOpt
