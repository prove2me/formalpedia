-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_klein
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.klein
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:44:53.665813+00:00
-- url     : https://prove2.me/theorems/7adef4d4-fdbe-47fc-910d-eb610fd91718
-- title:
--   Theorem 3: Klein inequality with equality
-- statement:
--   Let $A,B$ be positive definite matrices of the same size. With $H(A,B)=\operatorname{Tr}A(\log A-\log B)$,
--   $$H(A,B)\ge\operatorname{Tr}(A-B),\qquad H(A,B)=\operatorname{Tr}(A-B)\iff A=B.$$
--   No equality of traces or normalization is required. Klein’s inequality supplies the equality criterion used in the entropy inequalities.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 8, Theorem 3: Klein inequality with equality

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

/-- Theorem 3, PDF p.8: Klein's inequality and equality, with no trace normalization. -/
theorem klein [Nonempty A] (X Y : Mat A) (hX : X.PosDef) (hY : Y.PosDef) :
    (X - Y).trace.re ≤ (relativeEntropy X Y).toReal ∧
      ((relativeEntropy X Y).toReal = (X - Y).trace.re ↔ X = Y) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
