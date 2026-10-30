-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P02_conditionalTesting_classical_bounds
-- name    : QAlgorithms.Papers.Independent.Advance50.P02.conditionalTesting_classical_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:16:17.708598+00:00
-- url     : https://prove2.me/theorems/c042d45a-3ebd-4f4c-973a-a16ea6d356b3
-- title:
--   Four bounds for classical information
-- statement:
--   All Hilbert spaces are finite dimensional and complex; all logarithms are binary. Positive-operator inequalities use the identity when comparing with a scalar. Let $\rho_{XAB}=\sum_x|x\rangle\langle x|\otimes R^x_{AB}$ be normalized with positive blocks. Let $k$ count the labels with $\operatorname{tr}R^x>0$; then $k\ge1$. Use actual marginals and register permutations of this state. For $0\le\varepsilon\le1$,
--   $$
--   H_h^\varepsilon(A|B)\ge H_h^\varepsilon(A|XB)\ge H_h^\varepsilon(XA|B)-\log k,
--   $$
--   $$
--   H_h^\varepsilon(A|XB)\le H_h^\varepsilon(XA|B)\le H_h^\varepsilon(A|B)+\log k.
--   $$
--   These four inequalities quantify the cost of retaining a classical register.
-- source:
--   A Hierarchy of Information Quantities for Finite Block Length Analysis of Quantum Tasks, arXiv:1208.1478v3, PDF p. 9, Proposition 7: bounds for classical information

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

/-- Proposition 7, PDF pp.9--10: all four inequalities, support labels only. -/
theorem conditionalTesting_classical_bounds (blocks : X → Mat (A × B))
    (hblocks : NormalizedBlocks blocks) (e : ℝ) (he : 0 ≤ e ∧ e ≤ 1) :
    conditionalTesting e (conditionOnClassical blocks) ≤ conditionalTesting e (cqMarginal blocks) ∧
    conditionalTesting e (joinClassical blocks) - (logTwo (labelCount blocks) : ℝ) ≤
      conditionalTesting e (conditionOnClassical blocks) ∧
    conditionalTesting e (conditionOnClassical blocks) ≤ conditionalTesting e (joinClassical blocks) ∧
    conditionalTesting e (joinClassical blocks) ≤
      conditionalTesting e (cqMarginal blocks) + (logTwo (labelCount blocks) : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P02

end
