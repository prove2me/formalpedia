-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P74_coherent_mixture_chiSquare_kernel
-- name    : QAlgorithms.Papers.Independent.Intake100.P74.coherent_mixture_chiSquare_kernel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:00:21.654988+00:00
-- url     : https://prove2.me/theorems/2f887b01-f840-4acd-bdb2-8fad79a5a9e6
-- title:
--   Coherent-mixture quantum chi-square kernel
-- statement:
--   Let $P$ be a nonnegative probability density relative to planar Lebesgue measure on $\mathbb C$, let $\rho=\int P(z)|z\rangle\langle z|\,d^2z$, and let $N>0$. Write $\tau_N$ for the thermal state of mean photon number $N$ and $t_N=\sqrt{(N+1)/N}$. Then
--
--   $$
--   1+\chi^2(\rho,\tau_N)=\iint P(z)P(w)C_N(z,w)\,d^2z\,d^2w,
--   \quad C_N(z,w)=(N+1)e^{-|z|^2-|w|^2+2t_N\operatorname{Re}(z\overline w)}.
--   $$
--
--   The convention is $1+\chi^2=\operatorname{Tr}[\rho\tau_N^{-1/2}\rho\tau_N^{-1/2}]$, represented by the positive Fock-entry sum $\sum_{i,j}|\rho_{ij}|^2/\sqrt{\tau_i\tau_j}$. Both sides may be infinite; no finite-energy assumption is made. This supplies the quantum kernel used in the factorization.
-- source:
--   Coherent-state constellations and polar codes for thermal Gaussian channels, arXiv:1603.05970v3, PDF p. 8, Appendix A, Lemma 3: coherent-mixture quantum chi-square kernel

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

/-- PDF p.8, Lemma 3, (22): normalized positive-P mixture with planar
Lebesgue density; full Fock-entry chi-square sum, with no energy/finiteness
premise. Printed t_n is corrected to t_N by its definition and proof. -/
theorem coherent_mixture_chiSquare_kernel
    (N : ℝ) (hN : 0 < N) (mu : Measure ℂ) [IsProbabilityMeasure mu]
    (hDensity : mu ≪ volume) :
    1 + quantumChiSquare (positivePState mu) N =
      ∫⁻ t : ℂ × ℂ, ENNReal.ofReal (coherentCollisionKernel N t.1 t.2) ∂mu.prod mu := by sorry

end QAlgorithms.Papers.Independent.Intake100.P74

end
