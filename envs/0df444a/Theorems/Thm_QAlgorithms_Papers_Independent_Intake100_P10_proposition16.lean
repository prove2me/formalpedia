-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P10_proposition16
-- name    : QAlgorithms.Papers.Independent.Intake100.P10.proposition16
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:02:59.112926+00:00
-- url     : https://prove2.me/theorems/282918e3-a9dd-4d2b-ba85-e8569e9e78f7
-- title:
--   Restricted intrinsic steerability is monogamous
-- statement:
--   Let $X_1,X_2,A,C$ be finite nonempty alphabets and let $\hat\rho_B^{a,c,x_1,x_2}$ be an assemblage on a single arbitrary Bob system $B$. Suppose
--
--   $$\sum_c\hat\rho_B^{a,c,x_1,x_2}=\hat\theta_B^{a,x_1}\quad\text{independently of }x_2,\qquad\sum_a\hat\rho_B^{a,c,x_1,x_2}=\hat\kappa_B^{c,x_2}\quad\text{independently of }x_1.$$
--
--   For restricted intrinsic steerability in bits,
--
--   $$S^R(AC;B)_{\hat\rho}\ge S^R(A;B)_{\hat\theta}+S^R(C;B)_{\hat\kappa}.$$
--
--   The grouped functional on the left optimizes over every joint law of $X_1,X_2$. Both marginal assemblages retain the same Bob system.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, PDF p. 15, Proposition 16, (183)–(185)

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

/-- Proposition 16, PDF p.15, (183)--(185): ONE Bob system, with computed
marginals, and optimization over every joint input law. WARNING: (189)--(190)
uses a marginal BE constraint absent from grouped Definition 3. Independent
moderation is required; no extension-class-equality premise has been added. -/
theorem proposition16 (rho : AssemblageCoefficients (X1 × X2) (A1 × A2) B)
    (hrho : IsAssemblage rho) (hns : GroupedNoSignaling rho) :
    restrictedSteerability (firstGrouped rho) + restrictedSteerability (secondGrouped rho) ≤
      restrictedSteerability rho := by sorry

end Multipartite

end QAlgorithms.Papers.Independent.Intake100.P10

end
