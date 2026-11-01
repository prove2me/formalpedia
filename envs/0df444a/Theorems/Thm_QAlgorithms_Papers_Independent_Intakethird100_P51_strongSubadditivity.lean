-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_strongSubadditivity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.strongSubadditivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:43:16.56428+00:00
-- url     : https://prove2.me/theorems/99fe207b-befc-4d45-a88c-629615d2b5e3
-- title:
--   Theorem 1 and abstract capstone: strong subadditivity with exact equality condition
-- statement:
--   Let $\rho_{123}>0$ be a trace-one state of three finite systems, and let every subscript denote its partial trace. Operators in a logarithm identity are extended by identity operators to the full system. Then
--   $$S(\rho_{123})+S(\rho_2)\le S(\rho_{12})+S(\rho_{23}),$$
--   with equality if and only if
--   $$\log\rho_{123}-\log\rho_{12}=\log\rho_{23}-\log\rho_2.$$
--   This characterizes exact saturation of strong subadditivity.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 4, Theorem 1 and abstract capstone: strong subadditivity with exact equality condition

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

/-- Theorem 1 and (3)–(4), PDF pp.3–4,12–13: SSA with its exact log equality condition. -/
theorem strongSubadditivity [Nonempty A] [Nonempty B] [Nonempty C] (rho : Mat (A × (B × C))) (h : FaithfulDensity rho) :
    0 ≤ ssaGap rho ∧ (ssaGap rho = 0 ↔ SSAlogCondition rho) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
