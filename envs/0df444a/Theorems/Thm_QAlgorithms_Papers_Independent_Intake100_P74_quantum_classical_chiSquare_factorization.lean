-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P74_quantum_classical_chiSquare_factorization
-- name    : QAlgorithms.Papers.Independent.Intake100.P74.quantum_classical_chiSquare_factorization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:01:19.765081+00:00
-- url     : https://prove2.me/theorems/4bfc4d97-6d97-4dbb-b1ad-d2ca9dda08c6
-- title:
--   Quantum and classical chi-square factorization
-- statement:
--   Fix $0\le k\le1$, noise photon number $N_c\ge0$, and $N>0$. Let $U,V$ be independent real random variables with arbitrary probability laws. Form $Z=\sqrt{N/2}(U+iV)$ and pass $|Z\rangle$ through attenuation of amplitude $k$ followed by independent circular Gaussian noise of mean photon number $N_c$. Let $\rho$ be the resulting average Fock-space state and $N'=k^2N+N_c$. If $N'>0$, set
--
--   $$s=\frac{k^2N}{\sqrt{N'(N'+1)}-k^2N}.$$
--
--   Let $Y\sim\mathcal N(0,1+s)$ and let $Y'_1=\sqrt{s}U+G_1$, $Y'_2=\sqrt{s}V+G_2$, with independent standard normal noises independent of the inputs. Then
--
--   $$1+\chi^2(\rho,\tau_{N'})=(1+\chi^2(P_{Y'_1},P_Y))(1+\chi^2(P_{Y'_2},P_Y)).$$
--
--   The quantum convention is $\operatorname{Tr}[\rho\tau^{-1/2}\rho\tau^{-1/2}]-1$. All divergences may be infinite. If $N'=0$, $\rho$ is vacuum and its divergence from vacuum is zero. This includes pure loss and the $k=1$ additive-noise endpoint. The measure formulation includes densities and finite atomic constellations.
-- source:
--   Coherent-state constellations and polar codes for thermal Gaussian channels, arXiv:1603.05970v3, PDF p. 7, Appendix A, Lemma 1: quantum/classical chi-square factorization

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P74

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P74

open MeasureTheory

open scoped BigOperators ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient thermalMatrix)

open QAlgorithms.Papers.Independent.Support50.P14 (photonEnergy)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal spectralEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P39 (thermalProbability g)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.7--9, Lemma 1. Printed: arbitrary density variables, without an
explicit independence hypothesis. Changed: independent coordinate probability
laws. Why: Section 4 specifies independence and (32) factors their joint law.
The measure notation also makes the finite atomic specialization in (12)
well defined by integration of the same kernels; no moment condition is added.
Nc=0 includes pure loss without dividing by Nc. The replacing-vacuum endpoint
is separate from the SNR expression. -/
theorem quantum_classical_chiSquare_factorization
    (k Nc N : ℝ) (hk : 0 ≤ k) (hkUpper : k ≤ 1) (hNc : 0 ≤ Nc) (hN : 0 < N)
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (0 < k ^ 2 * N + Nc →
      1 + quantumChiSquare (constellationOutput k Nc N mu nu) (k ^ 2 * N + Nc) =
        (1 + classicalChiSquare (comparisonSnr k Nc N) mu) *
        (1 + classicalChiSquare (comparisonSnr k Nc N) nu)) ∧
    (k ^ 2 * N + Nc = 0 →
      constellationOutput k Nc N mu nu = thermalMatrix 1 ∧
      quantumChiSquare (constellationOutput k Nc N mu nu) 0 = 0) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P74

end
