-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_two_sample_gap
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.two_sample_gap
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:55:49.869001+00:00
-- url     : https://prove2.me/theorems/eb2038e7-24f8-446f-b689-f6cde41a46af
-- title:
--   §III C, Eqs.(30)–(31): two-dimensional example and information gap
-- statement:
--   Let two unit sample vectors have overlap magnitude $\cos(\theta/2)$ with $0<\theta<\pi$. They span a two-dimensional input space. With the first sample as anchor, put $P=\lvert\phi_1\rangle\langle\phi_1\rvert$ and $Q=\Pi_{\rm in}-P$. Then
--
--   $$\lambda_\perp=\cos^2\theta,\qquad \mathcal D_\perp(X)=\cos^2\theta\,QXQ,\qquad F(\mathcal E_U(\rho),U\rho U^\dagger)\ge1-(\cos\theta)^{2T}.$$
--
--   The fidelity bound holds for every supported density operator, target unitary and $T\ge0$. For $U(\alpha)=\exp(i\alpha P)$, $0\le\alpha<2\pi$, the pure output family from the second sample has quantum Fisher information
--
--   $$I_\alpha=4\bigl(\langle P^2\rangle_{\phi_2}-\langle P\rangle_{\phi_2}^2\bigr)=1-\lambda_\perp.$$
--
--   The identity links distinguishability to convergence. The identical-sample endpoint is not assigned dimension two.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 7, §III C, Eqs.(30)–(31): two-dimensional example and information gap

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.7–8, Eqs.(30)–(31): two-dimensional fidelity, compressed channel, and
quantum Fisher information (four times generator variance). The dimension-two promise
is made only for the strict interior overlap regime. -/
theorem two_sample_gap (phi : Fin 2 → EuclideanSpace ℂ I) (hphi : ∀ k, IsState (phi k))
    (theta : ℝ) (htheta : 0 < theta ∧ theta < Real.pi)
    (hoverlap : ‖inner ℂ (phi 0) (phi 1)‖ = Real.cos (theta / 2)) :
    lambdaPerp phi 0 = Real.cos theta ^ 2 ∧
    (∀ X : Matrix I I ℂ, let Q := samplePi (pureSamples phi) - pureDensity (phi 0)
      compressedReflectionChannel phi 0 X = (Real.cos theta ^ 2 : ℂ) • (Q * X * Q)) ∧
    (∀ (U : Matrix.unitaryGroup I ℂ) (rho : Matrix I I ℂ), IsDensityMatrix rho →
      InSampleSupport (pureSamples phi) rho → ∀ T : ℕ,
      1 - Real.cos theta ^ (2 * T) ≤
        rootFidelity (emulate phi 0 (U : Matrix I I ℂ) T rho) (densityConjugation (U : Matrix I I ℂ) rho)) ∧
    (∀ alpha : ℝ, 0 ≤ alpha → alpha < 2 * Real.pi →
      let family := fun t : ℝ => act (positivePhaseEvolution (pureDensity (phi 0)) t) (phi 1)
      let variance := (inner ℂ (phi 1) (act (pureDensity (phi 0) * pureDensity (phi 0)) (phi 1))).re -
        ((inner ℂ (phi 1) (act (pureDensity (phi 0)) (phi 1))).re) ^ 2
      DifferentiableAt ℝ family alpha ∧
        pureFisherInformation family alpha = 4 * variance ∧ 4 * variance = 1 - lambdaPerp phi 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
