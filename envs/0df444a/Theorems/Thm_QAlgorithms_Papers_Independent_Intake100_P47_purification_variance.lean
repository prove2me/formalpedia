-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_purification_variance
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.purification_variance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:37:59.700845+00:00
-- url     : https://prove2.me/theorems/de9bc728-a228-45d8-9fd9-018c6b8fb406
-- title:
--   Equation (3.15): variance duality
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. Let $\rho_{AB}$ be a state, $\tau_A\ge0$ cover $\rho_A$, and let $\rho_{ABC}$ be any normalized pure purification. Write $V(\rho_{AB}\|\tau_A)=\operatorname{tr}\rho_{AB}[\log\rho_{AB}-\log(\tau_A\otimes\rho_B)-D(\rho_{AB}\|\tau_A\otimes\rho_B)1]^2$. Then
--   $$V(\rho_{AC}\|\tau_A^{-1})=V(\rho_{AB}\|\tau_A).$$
--   The inverse is on support and $\tau_A$ need not be normalized. This explicit identity supplies the complementary-system variance used in the derivative-at-one argument.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 9, Equation (3.15): variance duality

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P47

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P47

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Topology

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P28 (SupportLE pinch logNonnegativeExtended)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy IsSupported)

open QAlgorithms.Papers.Independent.Bridge50.P49 (groupedProduct)

open QAlgorithms.Papers.Independent.Claimed50.P12 (DiagonalIn)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D I J : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype I] [Fintype J]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq I] [DecidableEq J]

/-- arXiv:1408.6894v5, PDF p.9, explicit equation (3.15); proof on p.24.
Variance duality is a conclusion, not a purification hypothesis. -/
theorem purification_variance [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Op (A × B)) (tau : Op A) (hr : IsDensityMatrix rho)
    (ht : tau.PosSemidef) (hS : SupportLE (traceRight rho) tau)
    (psi : EuclideanSpace ℂ ((A × B) × C)) (hp : IsState psi)
    (hpur : traceRight (pureDensity psi) = rho) :
    generalizedInformationVariance (pureAC psi) (supportPower tau (-1)) = generalizedInformationVariance rho tau := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
