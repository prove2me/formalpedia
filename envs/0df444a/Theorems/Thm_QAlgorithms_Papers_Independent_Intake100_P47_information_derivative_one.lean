-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_information_derivative_one
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.information_derivative_one
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:38:46.736815+00:00
-- url     : https://prove2.me/theorems/e1a2a6e2-44d8-40d4-97ee-ed00f9066948
-- title:
--   Proposition 11, explicit final clause: derivative at order one
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For a state $\rho_{AB}$ and a positive reference $\tau_A$ covering $\rho_A$, write $I_\alpha(\rho\|\tau)=\inf_{\sigma_B\in\mathcal S(B)}D_\alpha(\rho\|\tau\otimes\sigma_B)$ and $\widetilde I_\alpha$ for the analogous sandwiched quantity. Let $\rho_{AB},\tau_A$ be states with $\rho_A\ll\tau_A$. Let $V(\rho\|\tau)$ be the relative-information variance against $\tau_A\otimes\rho_B$. The finite real function of order is differentiable at one, with
--   $$\left.\frac{d}{d\alpha}\widetilde I_\alpha(\rho_{AB}\|\tau_A)\right|_{\alpha=1}=\frac12V(\rho_{AB}\|\tau_A).$$
--   This records only Proposition 11's independently meaningful final clause, with natural logarithms giving $\log e=1$. It does not assert the deferred optimizer formula at order $1/2$.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 11, Proposition 11, explicit final clause: derivative at order one

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

/-- arXiv:1408.6894v5, PDF p.11, ONLY Proposition 11's final clause;
independent argument on pp.28--29. Natural logarithms give log(e)=1.
The defective endpoint optimizer/envelope assertion is deferred separately. -/
theorem information_derivative_one [Nonempty A] [Nonempty B]
    (rho : Op (A × B)) (tau : Op A) (hr : IsDensityMatrix rho)
    (ht : IsDensityMatrix tau) (hS : SupportLE (traceRight rho) tau) :
    HasDerivAt (fun a : ℝ => (generalizedInformation true (a : RenyiOrder) rho tau).toReal)
      (generalizedInformationVariance rho tau / 2) 1 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
