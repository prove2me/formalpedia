-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P13_one_mode_thermal
-- name    : QAlgorithms.Papers.Independent.Gap48.P13.one_mode_thermal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T21:41:32.305048+00:00
-- url     : https://prove2.me/theorems/0339cb10-94e3-4bee-9008-613e6481e01c
-- title:
--   One-mode quasifree density, number mean, and entropy
-- statement:
--   Let $\lambda>0$ be the one-particle covariance on a one-dimensional complex Hilbert space. In the full oscillator representation, the statistical operator of the quasifree state $\omega_\lambda$ is
--
--   $$D_\lambda=\sum_{n=0}^\infty\frac1{1+\lambda}\left(\frac\lambda{1+\lambda}\right)^n|\phi_n\rangle\langle\phi_n|.$$
--
--   The sum converges in trace norm to a positive normalized density, and $\operatorname{Tr}(W(z)D_\lambda)=\exp(-|z|^2/2-\lambda|z|^2)$. Its finite number expectation and entropy in nats are
--
--   $$\omega_\lambda(a^+a)=\lambda,\qquad S(\omega_\lambda)=(\lambda+1)\log(\lambda+1)-\lambda\log\lambda.$$
--
--   The number expectation has an explicitly summable defining series. These identities retain all three scalar conclusions of the example without imposing a photon cutoff.
-- source:
--   Markov triplets on CCR-algebras, arXiv:0812.3724v2, PDF p. 10, Example 1.2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

/-- Example 1.2, PDF pp.10–11: the accepted full-Fock thermal density with photon
mean lambda; trace-norm diagonal sum, quasifree realization, mean, and nats entropy. -/
theorem one_mode_thermal (lambda : ℝ) (hlambda : 0 < lambda) :
    let D := QAlgorithms.Papers.Independent.Claimed50.P39.photonMeanThermalState lambda
    Osc.ThermalRealized (2 * lambda + 1) ∧
    Osc.DisplacementRealized ∧
    Osc.TraceHasSum (fun n : ℕ =>
      ((1 / (1 + lambda) * (lambda / (1 + lambda)) ^ n : ℝ) : ℂ) •
        Osc.fockDyad n n) D ∧
    (∀ z : ℂ, Osc.IsTraceClass ((Osc.displacement (-star z)).comp D) ∧
      Summable (fun n : ℕ => ((Osc.displacement (-star z)).comp D) (Osc.fockKet n) n) ∧
      Osc.fockTrace ((Osc.displacement (-star z)).comp D) =
        (Real.exp (-Complex.normSq z / 2 - lambda * Complex.normSq z) : ℂ)) ∧
    Summable (fun n : ℕ => (n : ℝ) * Osc.photonProbability D n) ∧
    Osc.photonMean D = lambda ∧
    QAlgorithms.Papers.Independent.Claimed50.P39.fockEntropyNats D =
      ENNReal.ofReal ((lambda + 1) * Real.log (lambda + 1) - lambda * Real.log lambda)
    := by sorry

end QAlgorithms.Papers.Independent.Gap48.P13

end
