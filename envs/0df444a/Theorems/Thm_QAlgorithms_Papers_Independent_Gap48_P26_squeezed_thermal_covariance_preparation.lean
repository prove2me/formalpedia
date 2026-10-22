-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_squeezed_thermal_covariance_preparation
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.squeezed_thermal_covariance_preparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:02:42.439646+00:00
-- url     : https://prove2.me/theorems/871e2f27-d859-44de-8e2e-6fbf91228d74
-- title:
--   Squeezed thermal covariance and correlated displacement preparation
-- statement:
--   Let $\kappa\ge1$ and $N\ge0$ be finite, and let $\rho(\kappa,N)$ be the two-mode squeezed output of a thermal state of mean $N$ tensored with vacuum. In the vacuum-$I$ covariance convention it is centered Gaussian, with $I=I_2$, $Z=\operatorname{diag}(1,-1)$ and
--
--   $$\gamma=\begin{pmatrix}aI&cZ\\cZ&bI\end{pmatrix},\quad a=2(N+1)\kappa-1,\quad b=2(N+1)\kappa-(2N+1),\quad c=2(N+1)\sqrt{\kappa(\kappa-1)}.$$
--   $$\gamma=\gamma_0+M,\quad\gamma_0=\gamma\big|_{N=0},\qquad M=2N\begin{pmatrix}\kappa I&\sqrt{\kappa(\kappa-1)}Z\\\sqrt{\kappa(\kappa-1)}Z&(\kappa-1)I\end{pmatrix}\succeq0.$$
--
--   The eigenvalues of $M$ are $2N(2\kappa-1)$ twice and zero twice, with an orthogonal diagonalization. More precisely,
--
--   $$\rho(\kappa,N)=\int D(\sqrt\kappa z)\otimes D(\sqrt{\kappa-1}\bar z)\,\rho(\kappa,0)\,[D(\sqrt\kappa z)\otimes D(\sqrt{\kappa-1}\bar z)]^*\,d\nu_N(z),$$
--
--   where $\nu_N$ is the circular Gaussian law of mean squared amplitude $N$, including the Dirac law at $N=0$. Every coefficient integral is integrable. Shared classical randomness and local displacements therefore prepare the state.
--
--   **Source correction.** The diagonalization sentence omits the factor $2N$ and repeated eigenvalues; these are restored.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 7, Eqs. (32)-(35)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P26

open MeasureTheory Filter

open scoped ENNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Next46.P32 (NumberString vacuum)

open QAlgorithms.Papers.Independent.Next46.P45 (entanglementOfFormation)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State rankOne IsDensity IsBarycenter IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation traceClassTensorPower weylCharacteristic boundedUnitaryConjugation
   conjugateKernel partialRight GaussianDensity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, (32)-(35): actual covariance and correlated-displacement preparation.
Printed diagonal diag(2 kappa-1,0) omits 2N and multiplicities: corrected below
are two eigenvalues 2N(2 kappa-1) and two zero eigenvalues. -/
theorem squeezed_thermal_covariance_preparation
    (kappa N : ℝ) (hk : 1 ≤ kappa) (hN : 0 ≤ N) :
    QAlgorithms.Papers.Independent.Claimed50.P19.GaussianWithCovariance
      (squeezedThermal kappa N) (squeezedCovariance kappa N) ∧
    (∀ v, QAlgorithms.Papers.Independent.Claimed50.P19.multimodeWeylTrace
      (squeezedThermal kappa N) v =
      QAlgorithms.Papers.Independent.Claimed50.P19.covarianceCharacteristicValue
        (squeezedCovariance kappa N) 0 v) ∧
    squeezedCovariance kappa N = squeezedCovariance kappa 0 + displacementCovariance kappa N ∧
    (displacementCovariance kappa N).PosSemidef ∧
    (∃ Q : QAlgorithms.Papers.Independent.Claimed50.P19.Cov 2,
      Q.transpose * Q = 1 ∧
      Q.transpose * displacementCovariance kappa N * Q =
        Matrix.diagonal (fun i : Fin 2 × Fin 2 =>
          if i.1 = 0 then 2 * N * (2 * kappa - 1) else 0)) ∧
    (∀ a b : NumberString 2,
      Integrable (fun z : ℂ => conjugateKernel (correlatedDisplacement kappa z)
        (squeezedThermal kappa 0) a b) (circularLaw N) ∧
      squeezedThermal kappa N a b = ∫ z : ℂ,
        conjugateKernel (correlatedDisplacement kappa z) (squeezedThermal kappa 0) a b
        ∂circularLaw N) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
