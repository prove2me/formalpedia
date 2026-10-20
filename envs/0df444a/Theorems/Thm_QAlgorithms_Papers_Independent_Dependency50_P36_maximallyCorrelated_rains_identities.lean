-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_maximallyCorrelated_rains_identities
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.maximallyCorrelated_rains_identities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:40:28.175175+00:00
-- url     : https://prove2.me/theorems/bb95df4b-a7a1-4602-8b12-88f708d7d30f
-- title:
--   Finite maximally correlated Rains optimizer and identities
-- statement:
--   Let $d\ge1$, let $\widetilde\rho$ be a positive semidefinite trace-one $d\times d$ matrix in fixed bases, and construct $\rho=\sum_{i,j}\widetilde\rho_{ij}|ii\rangle\langle jj|$. Let $\sigma=\Delta\rho$ be its full product-basis dephasing. Then $\sigma\in\mathrm{PPT}'$, its support contains that of $\rho$, and
--
--   $$R(\rho)=D(\rho\|\sigma)=I(A\rangle B)_\rho,\qquad V(\rho\|\sigma)=V(\rho\|I_A\otimes\rho_B).$$
--
--   Here $\mathrm{PPT}'=\{\tau\ge0:\|\tau^{T_B}\|_1\le1\}$, $R$ is the infimum of base-two relative entropy over this set, $I(A\rangle B)=S(B)-S(AB)$, and $V(\rho\|\tau)=\operatorname{Tr}\rho(\log_2\rho-\log_2\tau)^2-D(\rho\|\tau)^2$. Thus the constructed $\sigma$ is an actual Rains minimizer. These identities supply a concrete finite maximally correlated interface without claiming countable-support or infinite-dimensional extensions.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 9, Unnumbered maximally correlated Rains optimizer and entropy/variance identities

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P36

open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P63 (testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- Unnumbered MC identities, arXiv:1706.06221v3, PDF pp.9–10, around Proposition 10.
Coherent information agrees with the printed +D and Eq.(46); no infinite-dimensional claim. -/
theorem maximallyCorrelated_rains_identities {d : ℕ} (hd : 0 < d)
    (rhoTilde : Matrix (Fin d) (Fin d) ℂ) (hrho : IsDensityMatrix rhoTilde) :
    let rho := maximallyCorrelated rhoTilde
    let sigma := dephasing rho
    pptPrime sigma ∧ supportIncluded rho sigma ∧
      relativeEntropy rho sigma = rains rho ∧
      relativeEntropyFinite rho sigma = stateCoherentInformationBits rho ∧
      pairInformationVariance rho sigma = coherentVariance rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
