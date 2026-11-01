-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_productSSAEquality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.productSSAEquality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:48:04.625685+00:00
-- url     : https://prove2.me/theorems/779ca50a-f21c-4cc0-ba80-6f26a02571e1
-- title:
--   Section 2.2: product and split-middle equality cases
-- statement:
--   For a faithful trace-one tripartite state, the SSA entropy gap and the logarithm condition vanish whenever
--   $$\rho_{123}=\rho_1\otimes\rho_{23}\quad\text{or}\quad\rho_{123}=\rho_{12}\otimes\rho_3.$$
--   In particular this includes a product of three marginal states. More generally, if subsystem $2$ is $2'\otimes2''$, any faithful trace-one states $\alpha_{12'}$ and $\beta_{2''3}$ give equality for
--   $$\rho_{123}=\alpha_{12'}\otimes\beta_{2''3},$$
--   with canonical regrouping of the four factors. These are sufficient cases and are not claimed to exhaust equality.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 7, Section 2.2: product and split-middle equality cases

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P51

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakethird100.P51

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact interfaces from the frozen accepted library; no local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy marginalAB channelAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Gap48.P33 (measurementInformation)

section Statements

variable {A B C D J K O : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype J] [Fintype K] [Fintype O]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq J] [DecidableEq K] [DecidableEq O]

/-- Section 2.2, PDF p.7: all product and split-middle sufficient cases.
No tensor decomposition is asserted necessary. -/
theorem productSSAEquality [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] :
    (∀ rho : Mat (A × (B × C)), FaithfulDensity rho →
      (rho = Matrix.kronecker (traceRight (marginalAB rho)) (traceLeft rho) ∨
       rho = liftAB (marginalAB rho) * liftBC (Matrix.kronecker (1 : Mat B)
         (traceLeft (traceLeft rho)))) → ssaGap rho = 0 ∧ SSAlogCondition rho) ∧
    (∀ X : Mat (A × B), ∀ Y : Mat (D × C), FaithfulDensity X → FaithfulDensity Y →
      ssaGap (splitProduct X Y) = 0 ∧ SSAlogCondition (splitProduct X Y)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
