-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_gaussian_entropy_covariance_concativity
-- name    : QAlgorithms.Papers.Independent.Next46.P17.gaussian_entropy_covariance_concativity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:30:22.21298+00:00
-- url     : https://prove2.me/theorems/d9fc8905-fd72-4df4-bd01-3e1101a09b47
-- title:
--   Equation (88): gaussian entropy covariance concativity
-- statement:
--   Let $n\geq1$, $0<\lambda<1$, and let $\gamma_1,\gamma_2$ be physical $2n\times2n$ covariance matrices in the vacuum-$I$ convention: real symmetric positive definite matrices satisfying $\gamma_j\geq iJ$. Let $\rho[\gamma]$ be the centered Gaussian density constructed from its characteristic function. Then
--
--   $$
--   S(\rho[\lambda\gamma_1+(1-\lambda)\gamma_2])\geq\lambda S(\rho[\gamma_1])+(1-\lambda)S(\rho[\gamma_2]).
--   $$
--
--   This is entropy concativity as a function of covariance, with entropy in nats.
--
--   **Formalization Note** The literal printed density mixture is corrected by moving the covariance combination inside the Gaussian-state brackets, as pinned by the preceding sentence, (47), and Theorem VII.1. Independent moderation is pending.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 12, Equation (88), corrected intended covariance concativity

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17

noncomputable section

open Filter MeasureTheory

open scoped ENNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Next46.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19 (productWeyl FiniteMeanEnergy PhysicalCovariance Cov FockIndex covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

/-- PDF p.12, (88): covariance concativity with the uniquely pinned bracket correction.
Printed: S(lambda*rho[gamma1]+(1-lambda)*rho[gamma2]). Changed: place the
covariance mixture inside rho[...], as required by the preceding sentence,
Theorem VII.1, and (47). Independent moderation of the correction is pending. -/
theorem gaussian_entropy_covariance_concativity {n : ℕ} (hn : 0 < n)
    (lam : ℝ) (hlam : 0 < lam) (hlamOne : lam < 1)
    (gamma1 gamma2 : Cov n)
    (hGamma1 : PhysicalCovariance gamma1) (hGamma2 : PhysicalCovariance gamma2) :
    ENNReal.ofReal lam * extendedEntropyNats (gaussianCoefficient gamma1 0) +
      ENNReal.ofReal (1 - lam) * extendedEntropyNats (gaussianCoefficient gamma2 0) ≤
    extendedEntropyNats (gaussianCoefficient (lam • gamma1 + (1 - lam) • gamma2) 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
