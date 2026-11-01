-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_purifiedSSA
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.purifiedSSA
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:52:16.495781+00:00
-- url     : https://prove2.me/theorems/a20848b9-9203-40ce-bd38-d81d77451e10
-- title:
--   Equation (22): purified/weak-monotonicity form of SSA
-- statement:
--   Let $\rho_{1234}=|\psi\rangle\langle\psi|$ be any pure four-party state with $\|\psi\|=1$, and form all marginals by partial trace. Then
--   $$S(\rho_4)+S(\rho_2)\le S(\rho_{12})+S(\rho_{14}).$$
--   Under this purification the displayed inequality is equivalent to SSA for $\rho_{123}$. This records the purified weak-monotonicity form of SSA, including singular reduced states.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 9, Equation (22): purified/weak-monotonicity form of SSA

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

/-- Equation (22), PDF pp.9,15: the purified weak-monotonicity inequality and its
pointwise equivalence to SSA of the complementary triple. Equation (36) omits S
in print; (22) and the purification argument determine the entropy reading. -/
theorem purifiedSSA [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] (psi : EuclideanSpace ℂ (A × (B × (C × D)))) (h : ‖psi‖ = 1) :
    let rho := pureDensity psi
    WeakMonotonicity (marginalABD rho) ∧
      (0 ≤ ssaGap (marginalABC rho) ↔ WeakMonotonicity (marginalABD rho)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
