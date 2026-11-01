-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_purification
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.purification
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:50:00.407149+00:00
-- url     : https://prove2.me/theorems/bc3de5eb-6ffa-4a07-8ab1-a2728bb66f6c
-- title:
--   Section 3.3: purification and equality of complementary entropies
-- statement:
--   Every finite normalized positive semidefinite state $\rho_A$ has a finite nonzero auxiliary system $B$ and a unit vector $\psi_{AB}$ such that
--   $$\operatorname{Tr}_B|\psi\rangle\langle\psi|=\rho_A,\qquad S(\rho_B)=S(\rho_A).$$
--   Moreover, for every bipartite unit vector, its two reduced states have equal entropy. Singular states are permitted. The existence of the purification is part of the conclusion and supplies the complementary-entropy method.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 9, Section 3.3: purification and equality of complementary entropies

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

/-- Section 3.3, PDF p.9: purification exists; complementary entropies agree for
all unit bipartite pure states, including singular density matrices. -/
theorem purification [Nonempty A] [Nonempty B] (rho : Mat A) (h : IsDensityMatrix rho) :
    (∃ m : ℕ, 0 < m ∧ ∃ psi : EuclideanSpace ℂ (A × Fin m),
      ‖psi‖ = 1 ∧ traceRight (pureDensity psi) = rho ∧
        entropy (traceLeft (pureDensity psi)) = entropy rho) ∧
    (∀ psi : EuclideanSpace ℂ (A × B), ‖psi‖ = 1 →
      entropy (traceRight (pureDensity psi)) = entropy (traceLeft (pureDensity psi))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
