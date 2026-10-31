-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_cartanMembershipInsufficient
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.cartanMembershipInsufficient
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:57:02.642008+00:00
-- url     : https://prove2.me/theorems/82858d57-68b7-4916-b31b-6675ad70662e
-- title:
--   Two-qubit counterexamples to deciding inversion by Cartan membership
-- statement:
--   Consider the two-qubit Hamiltonians $H_{ZZ}=Z\otimes Z$, $H_{XX}=X\otimes X+Y\otimes Y$, and $H_{XXX}=X\otimes X+Y\otimes Y+Z\otimes Z$. They are all Hermitian and traceless. Define the concurrence involution by $\theta(A)=S\overline A S^\dagger$, where $S=(-iY)\otimes(-iY)$. Then
--
--   $$\theta(iH_{ZZ})=-iH_{ZZ},\quad\theta(iH_{XX})=-iH_{XX},\quad\theta(iH_{XXX})=-iH_{XXX}.$$
--
--   The first two Hamiltonians are type-I locally reversible, while the third is not. Thus membership in this same Cartan eigenspace does not determine local reversibility. The involution itself is not asserted to be a physical local operation.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 10, Time reversal and Cartan decompositions: eigenspace membership does not decide reversibility

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Negative conclusion on Cartan classification, PDF pp.10–11, pinned
to the explicit two-qubit ZZ, XX+YY, and XXX examples. All three iH
belong to the -1 concurrence eigenspace, with opposite reversibility outcomes.
This is not a claim about every possible algorithm using Cartan data. -/
theorem cartanMembershipInsufficient :
    IsHamiltonian (xyz 0 0 1) ∧ IsHamiltonian (xyz 1 1 0) ∧
    IsHamiltonian (xyz 1 1 1) ∧
    concurrenceInvolution (Complex.I • xyz 0 0 1) = -(Complex.I • xyz 0 0 1) ∧
    concurrenceInvolution (Complex.I • xyz 1 1 0) = -(Complex.I • xyz 1 1 0) ∧
    concurrenceInvolution (Complex.I • xyz 1 1 1) = -(Complex.I • xyz 1 1 1) ∧
    TypeI (xyz 0 0 1) ∧ TypeI (xyz 1 1 0) ∧ ¬ TypeI (xyz 1 1 1) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
