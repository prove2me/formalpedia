-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P76_two_qubit_bsa_unique_pure_residual
-- name    : QAlgorithms.Papers.Independent.Intake100.P76.two_qubit_bsa_unique_pure_residual
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T18:26:17.843989+00:00
-- url     : https://prove2.me/theorems/3c218552-9e07-4607-a030-9017bc672cf8
-- title:
--   Unique two-qubit BSA and a pure entangled residual
-- statement:
--   Let $\rho$ be a density matrix on $\mathbb C^2\otimes\mathbb C^2$. A best separable approximation is an unnormalized separable positive operator $S$ such that $\rho-S\succeq0$ and $\operatorname{Tr}S$ is maximal among all such operators. There exists exactly one such operator $S$. Set $\lambda=\operatorname{Tr}S$ and $R=\rho-S$. Then $0\leq\lambda\leq1$ and
--
--   $$R=0\quad\text{or}\quad R=(1-\lambda)|\psi_e\rangle\langle\psi_e|,\qquad 1-\lambda>0,$$
--
--   where $\psi_e$ is a unit vector that is not a product vector. The weighted operators $S$ and $R$ are unique. This is the operator interpretation of the optimal decomposition; normalized components with zero weight are not claimed unique.
-- source:
--   Separability and entanglement of composite quantum systems, arXiv:quant-ph/9707043v1, PDF p. 3, Unnumbered two-qubit BSA uniqueness and pure entangled remainder, Eq. (11)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P76

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate

open QAlgorithms QAlgorithms.Entanglement

namespace QAlgorithms.Papers.Independent.Intake100.P76

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B] [DecidableEq I]

/-- PDF p.3, Eq. (11), with the p.2 uniqueness preview: the unrestricted
optimal weighted operators are unique for two qubits, and a nonzero remainder
is a nonnegative multiple of one normalized entangled projector. No uniqueness
of inactive normalized components at weights zero or one is asserted. -/
theorem two_qubit_bsa_unique_pure_residual
    (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hrho : IsDensityMatrix rho) :
    ∃ S, IsBSA rho S ∧ (∀ T, IsBSA rho T → T = S) ∧
      0 ≤ S.trace.re ∧ S.trace.re ≤ 1 ∧
      (rho - S = 0 ∨
        ∃ psi : EuclideanSpace ℂ (Fin 2 × Fin 2),
          IsState psi ∧ ¬ IsUnitProduct psi ∧
          0 < 1 - S.trace.re ∧
          rho - S = ((1 - S.trace.re : ℝ) : ℂ) • pureDensity psi) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P76

end
