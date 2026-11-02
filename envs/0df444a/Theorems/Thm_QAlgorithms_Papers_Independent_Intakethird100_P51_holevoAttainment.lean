-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_holevoAttainment
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.holevoAttainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:02:37.026396+00:00
-- url     : https://prove2.me/theorems/873c8ced-48e8-4d21-b757-e85d3dd4945e
-- title:
--   Sections 7.1–7.3: Holevo bound is attainable iff active states commute
-- statement:
--   Fix a finite ensemble $\mathcal E=\{\pi_j,\rho_j\}$ of normalized PSD states with nonnegative weights summing to one. Its Holevo quantity is $\chi(\mathcal E)$ and $I(\mathcal E,\mathcal M)$ is the classical information extracted by a POVM. Then
--   $$\exists\,\mathcal M:\ I(\mathcal E,\mathcal M)=\chi(\mathcal E)\iff[\rho_j,\rho_k]=0\ \text{for all }\pi_j,\pi_k>0.$$
--   When the active states commute, a unitary simultaneous diagonalization gives a rank-one spectral projective measurement attaining equality. This is an existence and witness assertion, allowing singular states; it does not require every attaining POVM to be projective.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 17, Sections 7.1–7.3: Holevo bound is attainable iff active states commute

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

/-- Sections 7.1–7.3, PDF pp.17–20: existence of an attaining POVM iff active
states commute, and a simultaneous spectral projective witness in that case. -/
theorem holevoAttainment [Nonempty A] [Nonempty J] (w : J → ℝ) (hw : IsLaw w)
    (rho : J → Mat A) (hr : ∀ j, IsDensityMatrix (rho j)) :
    let commuting := ∀ j k, 0 < w j → 0 < w k → rho j * rho k = rho k * rho j
    ((∃ m : ℕ, 0 < m ∧ ∃ E : Fin m → Mat A, IsPOVM E ∧
      (Real.log 2 * measurementInformation w rho E) = holevo w rho) ↔ commuting) ∧
    (commuting → ∃ U : Mat A, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      (∀ j, 0 < w j → ∀ a b, a ≠ b → (Uᴴ * rho j * U) a b = 0) ∧
      IsPOVM (basisPVM U) ∧
      (∀ a b, basisPVM U a * basisPVM U b = if a = b then basisPVM U a else 0) ∧
      (Real.log 2 * measurementInformation w rho (basisPVM U)) = holevo w rho) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
