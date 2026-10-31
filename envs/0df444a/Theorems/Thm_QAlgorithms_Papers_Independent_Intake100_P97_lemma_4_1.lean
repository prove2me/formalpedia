-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P97_lemma_4_1
-- name    : QAlgorithms.Papers.Independent.Intake100.P97.lemma_4_1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:09:40.835505+00:00
-- url     : https://prove2.me/theorems/3609a470-6be4-479b-a537-9d2c8bcd27fb
-- title:
--   Lemma 4.1 (all three clauses)
-- statement:
--   Let $\Gamma$ be countably infinite, let $X=\mathbb R^\Gamma$ carry its product Borel sigma-algebra, and put $K=\ell^2_{\mathbb R}(\Gamma)$. A covariance is a bounded self-adjoint operator on $K$ bounded below by a positive multiple of the identity. Fix a covariance $D$. For every self-adjoint real trace-class operator $A$, the canonical completion $q_A$ of the finite-coordinate forms belongs to $L^1(\omega_D)$, agrees with $(x,Ax)$ on $K$, and
--
--   $$\|q_A\|_{L^1(\omega_D)}\le\|D\|\,\|A\|_1,\qquad \int_X q_A\,d\omega_D=\operatorname{tr}(DA).$$
--
--   It is the unique $L^1$ limit of those coordinate forms. If $A_t=A_t^*$ is trace class and differentiable in trace norm at $t_0$ with derivative $\dot A_{t_0}$, then
--
--   $$\left.\frac d{dt}q_{A_t}\right|_{t=t_0}=q_{\dot A_{t_0}}\quad\hbox{in }L^1(\omega_D).$$
--
--   Finally, for any real trace-class $A$ with $I-A$ invertible, $F(A)=\det(I-A)$ is Fréchet differentiable in trace norm and
--
--   $$DF_A(X)=-F(A)\operatorname{tr}((I-A)^{-1}X).$$
--
--   The last clause is stated equivalently by the usual uniform epsilon–delta remainder inequality in trace norm. This supplies the quadratic-completion and Fredholm differentiation interfaces.
-- source:
--   Entropic fluctuations in Gaussian dynamical systems, arXiv:1509.03244v1, PDF p. 16, Lemma 4.1 (all three clauses)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P97

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P97

open QAlgorithms.Papers.Independent.Next46.P02
  (IsModulusTraceClass modulusTraceNorm basisOperatorTrace hilbertPositiveSqrt)

variable {G : Type*} [Countable G] [Infinite G] [DecidableEq G]

/-- Lemma 4.1, all three clauses, PDF pp.16–17. Uniqueness means the canonical
L¹ completion of coordinate quadratic forms, not uniqueness among arbitrary
measurable functions agreeing on the potentially Gaussian-null subspace K.
Part (3) is the trace-norm Fréchet derivative in its epsilon–delta form. -/
theorem lemma_4_1 (e : ℕ ≃ G) (D : RealCoordinateOperator G) (hD : IsCovariance D) :
    (∀ A : RealCoordinateOperator G, ContinuousLinearMap.adjoint A = A → IsModulusTraceClass A →
      Integrable (gaussianQuadratic e A) (cylinderGaussian D) ∧
      ‖asL1 (cylinderGaussian D) (gaussianQuadratic e A)‖ ≤ ‖D‖ * modulusTraceNorm A ∧
      (∫ x, gaussianQuadratic e A x ∂cylinderGaussian D) = basisOperatorTrace (D * A) ∧
      (∀ v : RealCoordinateHilbert G, gaussianQuadratic e A (fun i => v i) = inner ℝ v (A v)) ∧
      Tendsto (fun n => asL1 (cylinderGaussian D) (finiteQuadratic e A n)) atTop
        (𝓝 (asL1 (cylinderGaussian D) (gaussianQuadratic e A))) ∧
      (∀ z : Lp ℝ 1 (cylinderGaussian D),
        Tendsto (fun n => asL1 (cylinderGaussian D) (finiteQuadratic e A n)) atTop (𝓝 z) →
          z = asL1 (cylinderGaussian D) (gaussianQuadratic e A))) ∧
    (∀ (A : ℝ → RealCoordinateOperator G) (Adot : RealCoordinateOperator G) (t0 : ℝ),
      (∀ t, ContinuousLinearMap.adjoint (A t) = A t) →
      HasBilateralTraceDerivative A Adot t0 →
      HasDerivAt (fun t => asL1 (cylinderGaussian D) (gaussianQuadratic e (A t)))
        (asL1 (cylinderGaussian D) (gaussianQuadratic e Adot)) t0) ∧
    (∀ A : RealCoordinateOperator G, IsModulusTraceClass A → IsUnit (1 - A) →
      ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧
        ∀ X : RealCoordinateOperator G, IsModulusTraceClass X → 0 < modulusTraceNorm X → modulusTraceNorm X < delta →
          |fredholmPlus (-(A + X)) - fredholmPlus (-A) +
            fredholmPlus (-A) * basisOperatorTrace (operatorInverse (1 - A) * X)| ≤
              epsilon * modulusTraceNorm X) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P97

end
