-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_goldenThompson
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.goldenThompson
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:45:46.854789+00:00
-- url     : https://prove2.me/theorems/6ddc1e94-e3d3-47f6-9976-6a199cc20e1e
-- title:
--   Theorem 4: Golden–Thompson–Symanzik and equality
-- statement:
--   For any two self-adjoint matrices $A,B$ on the same finite system,
--   $$\operatorname{Tr}e^{A+B}\le\operatorname{Tr}(e^Ae^B),$$
--   and equality holds if and only if $AB=BA$. This gives both the Golden–Thompson–Symanzik trace bound and its exact commutation criterion.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 8, Theorem 4: Golden–Thompson–Symanzik and equality

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

/-- Theorem 4, PDF p.8: Golden–Thompson–Symanzik with equality iff commutation. -/
theorem goldenThompson [Nonempty A] (X Y : Mat A) (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (NormedSpace.exp (X + Y)).trace.re ≤ (NormedSpace.exp X * NormedSpace.exp Y).trace.re ∧
      ((NormedSpace.exp (X + Y)).trace.re = (NormedSpace.exp X * NormedSpace.exp Y).trace.re ↔
        X * Y = Y * X) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
