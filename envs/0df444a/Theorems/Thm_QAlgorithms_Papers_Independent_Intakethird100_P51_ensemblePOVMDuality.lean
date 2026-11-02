-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_ensemblePOVMDuality
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.ensemblePOVMDuality
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:03:52.313523+00:00
-- url     : https://prove2.me/theorems/99f1c966-de71-4eb7-8c7d-ce65aac6552f
-- title:
--   Section 7.4: ensemble–POVM duality at a faithful average
-- statement:
--   Fix a faithful normalized state $\rho$. From any finite ensemble $\{\pi_j,\sigma_j\}$ with $\pi_j>0$ and average $\rho$, define
--   $$E_j=\pi_j\rho^{-1/2}\sigma_j\rho^{-1/2}.$$
--   These effects form a POVM. Conversely, for a POVM of nonzero effects, put
--   $$\tau_b=\operatorname{Tr}(E_b\rho)>0,\qquad\sigma_b=\tau_b^{-1}\sqrt\rho E_b\sqrt\rho.$$
--   The $\tau_b$ sum to one, every $\sigma_b$ is a density matrix, and $\sum_b\tau_b\sigma_b=\rho$. Both transformations are inverse, including recovery of the original weights and component states. This gives the normalized ensemble–POVM duality after deleting null entries.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 21, Section 7.4: ensemble–POVM duality at a faithful average

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

/-- Section 7.4, PDF p.21: positivity, normalization and both inverse properties
of the faithful-reference ensemble–POVM duality, after deleting null entries. -/
theorem ensemblePOVMDuality [Nonempty A] [Nonempty J] [Nonempty O] (rho : Mat A) (hr : FaithfulDensity rho) :
    (∀ w : J → ℝ, (∀ j, 0 < w j) → (∑ j, w j) = 1 →
      ∀ sigma : J → Mat A, (∀ j, IsDensityMatrix (sigma j)) → average w sigma = rho →
        IsPOVM (dualEffects rho w sigma) ∧
        (∀ j, effectProb (dualEffects rho w sigma j) rho = w j) ∧
        (∀ j, dualStates rho (dualEffects rho w sigma) j = sigma j)) ∧
    (∀ E : O → Mat A, IsPOVM E → (∀ b, E b ≠ 0) →
      (∀ b, 0 < effectProb (E b) rho) ∧
      IsLaw (fun b => effectProb (E b) rho) ∧
      (∀ b, IsDensityMatrix (dualStates rho E b)) ∧
      average (fun b => effectProb (E b) rho) (dualStates rho E) = rho ∧
      dualEffects rho (fun b => effectProb (E b) rho) (dualStates rho E) = E) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
