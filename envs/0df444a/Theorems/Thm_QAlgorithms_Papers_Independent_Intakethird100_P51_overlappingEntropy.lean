-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_overlappingEntropy
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.overlappingEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:55:20.173348+00:00
-- url     : https://prove2.me/theorems/a121daae-58d6-4dcb-b51d-99f44b053a24
-- title:
--   Equation (29): Araki–Lieb overlapping-subsystem entropy bound
-- statement:
--   Let $\rho_{123}>0$ have trace one on three finite systems, with reduced states $\rho_{12}$ and $\rho_{23}$. Then
--   $$S(\rho_{123})\le S(\rho_{12})+S(\rho_{23}).$$
--   This is the overlapping-subsystem inequality (29); the trace-one constraint is essential to the source’s statement.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 12, Equation (29): Araki–Lieb overlapping-subsystem entropy bound

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

/-- Equation (29), PDF p.12: the overlapping-subsystem bound, with trace one. -/
theorem overlappingEntropy [Nonempty A] [Nonempty B] [Nonempty C] (rho : Mat (A × (B × C))) (h : FaithfulDensity rho) :
    entropy rho ≤ entropy (marginalAB rho) + entropy (traceLeft rho) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
