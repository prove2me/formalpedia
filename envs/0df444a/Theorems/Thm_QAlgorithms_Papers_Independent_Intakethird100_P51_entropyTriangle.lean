-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_entropyTriangle
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.entropyTriangle
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:51:23.067093+00:00
-- url     : https://prove2.me/theorems/3e8bab3e-a92e-41f9-93d9-e762ff30ff74
-- title:
--   Equation (21): entropy triangle inequality
-- statement:
--   For any normalized positive semidefinite bipartite state $\rho_{12}$, let $\rho_1,\rho_2$ be its partial traces. Then
--   $$|S(\rho_1)-S(\rho_2)|\le S(\rho_{12})\le S(\rho_1)+S(\rho_2).$$
--   Pure and singular states are included. This is the full two-sided entropy triangle inequality.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 9, Equation (21): entropy triangle inequality

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

/-- Equation (21), PDF p.9: both sides of the entropy triangle inequality. -/
theorem entropyTriangle [Nonempty A] [Nonempty B] (rho : Mat (A × B)) (h : IsDensityMatrix rho) :
    |entropy (traceRight rho) - entropy (traceLeft rho)| ≤ entropy rho ∧
      entropy rho ≤ entropy (traceRight rho) + entropy (traceLeft rho) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
