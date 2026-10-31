-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition11
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition11
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:58:56.823806+00:00
-- url     : https://prove2.me/theorems/d0aaedb5-1688-4961-8bb9-fa94c283bf70
-- title:
--   Intrinsic steerability is superadditive
-- statement:
--   Let $X_1,X_2,A_1,A_2$ be finite nonempty alphabets and let $\hat\rho^{a_1,a_2,x_1,x_2}_{B_1B_2}$ be an assemblage on arbitrary Hilbert spaces $B_1,B_2$. Suppose its additional full Bob-operator marginal constraints hold:
--
--   $$\sum_{a_2}\hat\rho^{a_1,a_2,x_1,x_2}=\theta_{B_1B_2}^{a_1,x_1}\quad\text{independently of }x_2,$$
--   $$\sum_{a_1}\hat\rho^{a_1,a_2,x_1,x_2}=\kappa_{B_1B_2}^{a_2,x_2}\quad\text{independently of }x_1.$$
--
--   Define the local assemblages by $\hat\theta_{B_1}^{a_1,x_1}=\operatorname{Tr}_{B_2}\theta_{B_1B_2}^{a_1,x_1}$ and $\hat\kappa_{B_2}^{a_2,x_2}=\operatorname{Tr}_{B_1}\kappa_{B_1B_2}^{a_2,x_2}$. For Definition 1 with binary logarithms,
--
--   $$S(\hat\rho)\ge S(\hat\theta)+S(\hat\kappa).$$
--
--   There is no product-state hypothesis. The marginal assemblages are constructed from the joint assemblage by summing and taking actual partial traces.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 10, Proposition 11, (120)

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

/-- Proposition 11, PDF pp.10--12, (120): printed full Bob-marginal constraints,
with computed local assemblages and no product assumption. WARNING: the proof
uses componentwise BE no-signaling not explicitly required by Definition 1;
no stronger extension premise has been inserted. Independent moderation needed. -/
theorem proposition11 (rho : AssemblageCoefficients (X1 × X2) (A1 × A2) (B1 × B2))
    (hrho : IsAssemblage rho) (hns : GroupedNoSignaling rho) :
    intrinsicSteerability (firstReduced rho) + intrinsicSteerability (secondReduced rho) ≤
      intrinsicSteerability rho := by sorry

end Multipartite

end QAlgorithms.Papers.Independent.Intake100.P10

end
