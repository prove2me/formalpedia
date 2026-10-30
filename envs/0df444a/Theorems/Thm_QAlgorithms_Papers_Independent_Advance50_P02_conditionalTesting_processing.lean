-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_conditionalTesting_processing
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.conditionalTesting_processing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:15:24.444989+00:00
-- url     : https://prove2.me/theorems/15b077f3-916a-49d4-bc5c-e398c874d8b4
-- title:
--   Conditional testing entropy data processing
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho_{AB}$ be normalized, $\mathcal E:A\to A'$ a sub-unital trace-preserving completely positive map, and $\mathcal F:B\to B'$ a trace-preserving completely positive map. Put $\tau=(\mathcal E\otimes\mathcal F)(\rho)$. For $0\le\varepsilon\le1$,
--   $$H_h^\varepsilon(A|B)_\rho\le H_h^\varepsilon(A'|B')_\tau.$$
--   Here $H_h^\varepsilon$ optimizes $-D_h^\varepsilon(\rho\Vert I_A\otimes\sigma_B)$ over normalized $\sigma_B$. The statement uses this defining optimization and does not depend on the ambiguous printed dual endpoint.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 9, Proposition 4: conditional testing data processing

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P02

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Advance50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63
  (Mat tensorPower logTwo normalQuantile testingBeta)

open QAlgorithms.Papers.Independent.Information100.P71 (SupportIncluded supportPower)

open QAlgorithms (effectProb)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P67 (purifiedDistance)

open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)

open QAlgorithms.Papers.Independent.Dependency50.P28 (pinch)

variable {I J A B X Z : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
  [Fintype Z] [DecidableEq Z]

/-- Proposition 4, PDF p.9: separate local operations. -/
theorem conditionalTesting_processing (rho : Mat (A × B)) (hrho : QAlgorithms.IsDensityMatrix rho)
    (E : Mat A →ₗ[ℂ] Mat I) (F : Mat B →ₗ[ℂ] Mat J)
    (hE : QAlgorithms.Entanglement.IsCompletelyPositive E)
    (hF : QAlgorithms.Entanglement.IsCompletelyPositive F)
    (htpE : TracePreserving E) (htpF : TracePreserving F) (hsub : Below (E 1) 1)
    (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) :
    conditionalTesting e rho ≤ conditionalTesting e (tensorMap E F rho) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
