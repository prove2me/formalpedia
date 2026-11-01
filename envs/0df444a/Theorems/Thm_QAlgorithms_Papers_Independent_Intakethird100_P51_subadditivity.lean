-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_subadditivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.subadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:54:28.777201+00:00
-- url     : https://prove2.me/theorems/fe2f156c-3538-4c34-9cfa-fbcb5a760230
-- title:
--   Section 4 and equation (28): subadditivity with product equality
-- statement:
--   For a strictly positive trace-one bipartite state $\rho_{12}$, with actual marginal states $\rho_1,\rho_2$,
--   $$S(\rho_{12})\le S(\rho_1)+S(\rho_2),$$
--   and equality holds if and only if $\rho_{12}=\rho_1\otimes\rho_2$. This characterizes saturation of subadditivity by product states.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 12, Section 4 and equation (28): subadditivity with product equality

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

/-- Section 4, equation (28), PDF pp.11–12: subadditivity with product equality. -/
theorem subadditivity [Nonempty A] [Nonempty B] (rho : Mat (A × B)) (h : FaithfulDensity rho) :
    entropy rho ≤ entropy (traceRight rho) + entropy (traceLeft rho) ∧
      (entropy rho = entropy (traceRight rho) + entropy (traceLeft rho) ↔
        rho = Matrix.kronecker (traceRight rho) (traceLeft rho)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
