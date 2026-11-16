-- Prove2me | Theorems.Thm_QMatVecLB_ConvexOpt_Supplement_lemma_5_5
-- name    : QMatVecLB.ConvexOpt.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:24:36.745577+00:00
-- url     : https://prove2.me/theorems/d6d7ae4c-b0c8-403c-85fb-5ef995b154f1
-- title:
--   Lemma 5.5 — correlation ratio for the squared-determinant threshold
-- statement:
--   Let $\mathbb E$ be expectation over an $n\times n$ matrix $A$ with independent $N(0,1)$ entries, let $q(X)=e^{\langle X,X\rangle/2}\det(\partial_X)^2e^{-\langle X,X\rangle/2}$ (Eq. (56)), and for $\theta>0$ let $D_\theta(A)=\mathbf 1_{(\det A)^2\ge\theta}$. Then for every $n\ge1$,
--   $$\sup_{\theta>0}\frac{|\mathbb E[q(A)D_\theta(A)]|}{\mathbb E|q(A)|}\ \ge\ \frac{\mathbb E[q(A)^2]^{3/2}}{8\,\mathbb E[(\det A)^6]}=\frac{6}{\sqrt{n+1}\,(n+2)^2(n+3)(n+4)},$$
--   and this closed form is $\Omega(n^{-9/2})$: there is $c>0$ with $\frac{6}{\sqrt{n+1}(n+2)^2(n+3)(n+4)}\ge c\,n^{-9/2}$ for all $n\ge1$.
--
--   The ratio is the correlation-to-mass ratio of the witness $\beta^{(2)}$ of Section 5.2 against a threshold of $(\det A)^2$; it drives the magnitude lower bound, Theorem 5.6.
--
--   Differences from the source:
--   - encoding: sup_{θ>0} R(θ) ≥ V → ∀ r < V, ∃ θ > 0, r < R(θ); reason: this is exactly the supremum inequality in the extended reals, with no boundedness assumption
--   - encoding: E over i.i.d. N(0,1) entries; q of Eq. (56) → integrals against GaussianMatrix.gaussianMatrix n n; the published q; reason: the Section 5 convention and the base definitions
--   - encoding: E[q²]^{3/2} → Real.rpow (∫ q²) (3/2); reason: E[q²] ≥ 0, so rpow is the real power
--   - encoding: = Ω(n^{−9/2}) → ∃ c > 0, ∀ n ≥ 1, c·n^{−9/2} ≤ 6/(√(n+1)(n+2)²(n+3)(n+4)); reason: the asymptotic claim about the closed form, as a separate conjunct uniform in n
--   - encoding: n × n matrices with n a positive integer → hypothesis 1 ≤ n; reason: excludes only the degenerate case
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, Lemma 5.5, PDF p. 14 (printed p. 13).

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_QMatVecLB_ConvexOpt_Supplement_Witness

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
set_option autoImplicit false

namespace QMatVecLB.ConvexOpt.Supplement
attribute [local instance] Classical.propDecidable

theorem lemma_5_5 :
    (∀ n : ℕ, 1 ≤ n →
      (∀ r : ℝ,
        r < Real.rpow (∫ A : RMat n, q A ^ 2 ∂GaussianMatrix.gaussianMatrix n n) ((3 : ℝ) / 2) /
            (8 * ∫ A : RMat n, A.det ^ 6 ∂GaussianMatrix.gaussianMatrix n n) →
        ∃ θ : ℝ, 0 < θ ∧
          r < |∫ A : RMat n, q A * detSqDecision θ A ∂GaussianMatrix.gaussianMatrix n n| /
            ∫ A : RMat n, |q A| ∂GaussianMatrix.gaussianMatrix n n) ∧
      Real.rpow (∫ A : RMat n, q A ^ 2 ∂GaussianMatrix.gaussianMatrix n n) ((3 : ℝ) / 2) /
          (8 * ∫ A : RMat n, A.det ^ 6 ∂GaussianMatrix.gaussianMatrix n n) =
        6 / (Real.sqrt ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) * ((n : ℝ) + 4))) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * (n : ℝ) ^ (-(9 : ℝ) / 2) ≤
        6 / (Real.sqrt ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2 * ((n : ℝ) + 3) * ((n : ℝ) + 4))) := by sorry

end QMatVecLB.ConvexOpt.Supplement
