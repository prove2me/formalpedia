-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_lindbladDilation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.lindbladDilation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:53:09.259432+00:00
-- url     : https://prove2.me/theorems/f97c46dc-9fd1-487e-9b69-d02d71ddee8e
-- title:
--   Section 3.4: Lindblad dilation, Kraus isometry, and entropy preservation
-- statement:
--   Every finite CPTP endomorphism $\Phi$ on $A$ admits a finite auxiliary system $B$, a unit vector $\beta_B$ and a unitary $U_{AB}$ such that for every operator $X$,
--   $$\Phi(X)=\operatorname{Tr}_B\bigl[U_{AB}(X\otimes|\beta\rangle\langle\beta|)U_{AB}^{\dagger}\bigr].$$
--   For any finite normalized rectangular Kraus family $F_k:A\to A'$, define $V_{(a',k),a}=(F_k)_{a',a}$. Then
--   $$V^{\dagger}V=I,\quad\operatorname{Tr}_B(VXV^{\dagger})=\sum_kF_kXF_k^{\dagger},\quad S(V\rho V^{\dagger})=S(\rho).$$
--   For every density matrix $\rho$, $V\rho V^{\dagger}$ and $\rho$ have the same nonzero eigenvalues with multiplicity. Only the endomorphism clause asserts a unitary on a single space.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 10, Section 3.4: Lindblad dilation, Kraus isometry, and entropy preservation

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

/-- Section 3.4, equations (24)–(26), PDF pp.10–11: unitary endomorphism dilation
and rectangular Kraus isometry, with entropy and nonzero-spectrum preservation. -/
theorem lindbladDilation [Nonempty A] [Nonempty B] [Nonempty K] :
    (∀ Phi : Superop A A, IsChannel Phi →
      ∃ m : ℕ, 0 < m ∧ ∃ beta : EuclideanSpace ℂ (Fin m), ‖beta‖ = 1 ∧
        ∃ U : Mat (A × Fin m), Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
          ∀ X : Mat A, Phi X = traceRight (U * Matrix.kronecker X (pureDensity beta) * Uᴴ)) ∧
    (∀ F : K → Matrix B A ℂ, IsKrausFamily F →
      (krausV F)ᴴ * krausV F = 1 ∧
      (∀ X : Mat A, traceRight (krausV F * X * (krausV F)ᴴ) = krausApply F X) ∧
      (∀ rho : Mat A, IsDensityMatrix rho →
        entropy (krausV F * rho * (krausV F)ᴴ) = entropy rho ∧
        ∀ z : ℂ, z ≠ 0 →
          Module.finrank ℂ (Module.End.eigenspace (krausV F * rho * (krausV F)ᴴ).mulVecLin z) =
          Module.finrank ℂ (Module.End.eigenspace rho.mulVecLin z))) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
