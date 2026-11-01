-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P54_symmetric_gaussian_invariance
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P54.symmetric_gaussian_invariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:43:47.054879+00:00
-- url     : https://prove2.me/theorems/235986eb-f8e9-4bf6-a2f5-48a4ae426348
-- title:
--   Appendix A: symmetric Gaussian invariance and second moment
-- statement:
--   Let $D\ge1$ and $\sigma^2>0$. In $\mathbb C^D$, let $\Gamma$ have independent centered complex Gaussian coordinates, each with variance $\sigma^2/D$: equivalently, its $2D$ real and imaginary coordinates are independent $N(0,\sigma^2/(2D))$ variables. Then
--
--   $$\mathcal L(U\Gamma)=\mathcal L(\Gamma)\quad\text{for every unitary }U,\qquad
--   \mathbb E\|\Gamma\|_2^2=\sigma^2.$$
--
--   The squared norm is integrable. This makes the symmetric centered law independent of the chosen orthonormal basis. Definition 22's printed means are read as zero by the immediately preceding prose; no noncentered covariance assertion is used.
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, PDF p. 14, Appendix A: symmetric Gaussian invariance and second moment

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal

open MeasureTheory ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P54

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

/-- Appendix A, PDF p.14: unitary invariance and the total second moment of the CENTERED
symmetric Gaussian. Integrability is stated explicitly, avoiding default-zero expectations. -/
theorem symmetric_gaussian_invariance {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] (D : ℕ) (hD : 0 < D)
    (s2 : ℝ≥0) (hs : 0 < s2) (G : Omega → EuclideanSpace ℂ (Fin D))
    (hG : SymmetricGaussian mu D s2 G) :
    (∀ U : Matrix.unitaryGroup (Fin D) ℂ,
      Measure.map (fun w => act (U : Matrix (Fin D) (Fin D) ℂ) (G w)) mu = Measure.map G mu) ∧
    Integrable (fun w => ‖G w‖ ^ 2) mu ∧ (∫ w, ‖G w‖ ^ 2 ∂mu) = s2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P54

end
