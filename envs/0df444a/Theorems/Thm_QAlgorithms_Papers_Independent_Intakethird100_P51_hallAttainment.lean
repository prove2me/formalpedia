-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_hallAttainment
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.hallAttainment
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:05:23.437257+00:00
-- url     : https://prove2.me/theorems/c4a862b6-c4cd-4b1b-a165-6bb611d017e6
-- title:
--   Section 7.4: attainability of Hall bound and commutation consequence
-- statement:
--   Fix a faithful density matrix $\rho$ and a finite POVM $\{E_b\}$, allowing zero or singular effects. Let $Q_b=\sqrt\rho E_b\sqrt\rho$, and let $B_{\rm Hall}(\rho,\mathcal M)$ be Hall’s right side with null outcomes deleted. Then
--   $$\exists\,\mathcal E\text{ of average }\rho:\ I(\mathcal E,\mathcal M)=B_{\rm Hall}(\rho,\mathcal M)\iff[Q_b,Q_c]=0\quad\forall b,c.$$
--   Moreover, this commutation implies $[\rho,E_b]=0$ for every $b$. The ensemble varies subject to its average; no channel-image constraint is imposed.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 21, Section 7.4: attainability of Hall bound and commutation consequence

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

/-- Section 7.4, PDF p.21: existence of an attaining ensemble for fixed rho,E,
with the commutation consequence; the ensemble is varied subject to its average. -/
theorem hallAttainment [Nonempty A] [Nonempty O] (rho : Mat A) (hr : FaithfulDensity rho) (E : O → Mat A) (hE : IsPOVM E) :
    let commuting := ∀ b c, dualUnnormalized rho E b * dualUnnormalized rho E c =
      dualUnnormalized rho E c * dualUnnormalized rho E b
    ((∃ m : ℕ, 0 < m ∧ ∃ w : Fin m → ℝ, IsLaw w ∧
      ∃ sigma : Fin m → Mat A, (∀ j, IsDensityMatrix (sigma j)) ∧ average w sigma = rho ∧
        (Real.log 2 * measurementInformation w sigma E) = hallBound rho E) ↔ commuting) ∧
    (commuting → ∀ b, rho * E b = E b * rho) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
