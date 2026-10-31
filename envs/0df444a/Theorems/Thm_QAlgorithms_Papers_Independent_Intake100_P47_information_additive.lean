-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P47_information_additive
-- name    : QAlgorithms.Papers.Independent.Intake100.P47.information_additive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:26:59.902431+00:00
-- url     : https://prove2.me/theorems/c18ba0c9-7afa-4650-9397-4d43ba815be0
-- title:
--   Lemma 7: Additivity for both generalized informations
-- statement:
--   All Hilbert spaces are finite dimensional and nonzero. States are positive semidefinite operators of trace one, logarithms are natural, and $\rho\ll\sigma$ means inclusion of supports. Write $D_\alpha$ and $\widetilde D_\alpha$ for the Petz and sandwiched divergences, respectively, with generalized inverse powers on support and orders $0,1,\infty$ defined by limits. For a state $\rho_{AB}$ and a positive reference $\tau_A$ covering $\rho_A$, write $I_\alpha(\rho\|\tau)=\inf_{\sigma_B\in\mathcal S(B)}D_\alpha(\rho\|\tau\otimes\sigma_B)$ and $\widetilde I_\alpha$ for the analogous sandwiched quantity. Let $\rho_{AB}$ and $\omega_{A'B'}$ be states, and let $\tau_A,\kappa_{A'}\ge0$ cover their respective marginals. Then
--   $$I_\alpha(\rho\otimes\omega\|\tau\otimes\kappa)=I_\alpha(\rho\|\tau)+I_\alpha(\omega\|\kappa)\quad(\alpha\ge0),$$
--   $$\widetilde I_\alpha(\rho\otimes\omega\|\tau\otimes\kappa)=\widetilde I_\alpha(\rho\|\tau)+\widetilde I_\alpha(\omega\|\kappa)\quad(\alpha\ge1/2).$$
--   The joint tensor factors are regrouped as $AA':BB'$. References need not have trace one. Taking marginal or identity references yields the stated additivity specializations for mutual information and conditional entropy.
-- source:
--   Correlation Detection and an Operational Interpretation of the Renyi Mutual Information, arXiv:1408.6894v5, PDF p. 10, Lemma 7: Additivity for both generalized informations

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

/-- arXiv:1408.6894v5, PDF p.10, Lemma 7, (3.16)--(3.17).
The two references may have arbitrary positive trace. Marginal-reference mutual
informations and identity-reference conditional entropies specialize these identities. -/
theorem information_additive [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (rho : Op (A × B)) (omega : Op (C × D)) (tau : Op A) (kappa : Op C)
    (hr : IsDensityMatrix rho) (hw : IsDensityMatrix omega)
    (ht : tau.PosSemidef) (hk : kappa.PosSemidef)
    (hS : SupportLE (traceRight rho) tau) (hT : SupportLE (traceRight omega) kappa) :
    (∀ a : RenyiOrder, 0 ≤ a →
      generalizedInformation false a (groupedProduct rho omega) (Matrix.kronecker tau kappa) =
        generalizedInformation false a rho tau + generalizedInformation false a omega kappa) ∧
    (∀ a : RenyiOrder, ((1/2 : ℝ) : RenyiOrder) ≤ a →
      generalizedInformation true a (groupedProduct rho omega) (Matrix.kronecker tau kappa) =
        generalizedInformation true a rho tau + generalizedInformation true a omega kappa) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P47

end
