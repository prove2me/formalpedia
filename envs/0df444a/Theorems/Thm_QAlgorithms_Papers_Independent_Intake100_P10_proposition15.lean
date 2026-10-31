-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition15
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition15
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:01:41.462347+00:00
-- url     : https://prove2.me/theorems/4c45df50-5c1a-4bb4-a923-3d4f8405f385
-- title:
--   Restricted superadditivity and product additivity
-- statement:
--   Let $X_1,X_2,A_1,A_2$ be finite nonempty alphabets and let $\hat\rho^{a_1,a_2,x_1,x_2}_{B_1B_2}$ be an assemblage on arbitrary Hilbert spaces $B_1,B_2$. Suppose its additional full Bob-operator marginal constraints hold:
--
--   $$\sum_{a_2}\hat\rho^{a_1,a_2,x_1,x_2}=\theta_{B_1B_2}^{a_1,x_1}\quad\text{independently of }x_2,$$
--   $$\sum_{a_1}\hat\rho^{a_1,a_2,x_1,x_2}=\kappa_{B_1B_2}^{a_2,x_2}\quad\text{independently of }x_1.$$
--
--   Define the local assemblages by $\hat\theta_{B_1}^{a_1,x_1}=\operatorname{Tr}_{B_2}\theta_{B_1B_2}^{a_1,x_1}$ and $\hat\kappa_{B_2}^{a_2,x_2}=\operatorname{Tr}_{B_1}\kappa_{B_1B_2}^{a_2,x_2}$. For Definition 3 with binary logarithms,
--
--   $$S^R(\hat\rho)\ge S^R(\hat\theta)+S^R(\hat\kappa).$$
--
--   If the joint assemblage is a product $\hat\rho^{a_1,a_2,x_1,x_2}=\hat\theta^{a_1,x_1}_{B_1}\otimes\hat\kappa^{a_2,x_2}_{B_2}$ of assemblages, then also
--
--   $$S^R(\hat\rho)=S^R(\hat\theta)+S^R(\hat\kappa).$$
--
--   The joint supremum still ranges over all joint input laws, including correlated choices. This retains both conclusions across the page break.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 13, Proposition 15, (162)–(165)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P10

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (PositiveTraceClass operatorTrace partialTraceFirst partialTraceSecond IsQuantumOperation)

open QAlgorithms.Papers.Independent.Renew46.P08 (qcmi)

open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

section Multipartite

variable {X1 X2 A1 A2 B1 B2 B : Type}

variable [Fintype X1] [Fintype X2] [Fintype A1] [Fintype A2]

variable [Nonempty X1] [Nonempty X2] [Nonempty A1] [Nonempty A2]

/-- Proposition 15, PDF pp.13--15, (162)--(165): BOTH superadditivity and
product equality. Grouped Definition 3 remains unchanged; its extension proof
convention requires independent moderation. The product supremum permits every
joint input law, including correlated laws. -/
theorem proposition15 (rho : AssemblageCoefficients (X1 × X2) (A1 × A2) (B1 × B2))
    (hrho : IsAssemblage rho) (hns : GroupedNoSignaling rho) :
    (restrictedSteerability (firstReduced rho) + restrictedSteerability (secondReduced rho) ≤
      restrictedSteerability rho) ∧
    (∀ (theta : AssemblageCoefficients X1 A1 B1) (kappa : AssemblageCoefficients X2 A2 B2),
      IsAssemblage theta → IsAssemblage kappa → rho = productFamily theta kappa →
      restrictedSteerability rho = restrictedSteerability theta + restrictedSteerability kappa) := by sorry

end Multipartite

end QAlgorithms.Papers.Independent.Intake100.P10

end
