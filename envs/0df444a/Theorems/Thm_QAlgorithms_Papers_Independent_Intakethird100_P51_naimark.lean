-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_naimark
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.naimark
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:53:47.297914+00:00
-- url     : https://prove2.me/theorems/4be28d7e-d6e1-4db0-8960-23d76249dcf4
-- title:
--   Section 3.5: computed projective representation of a POVM
-- statement:
--   Let $\{E_b\}$ be a finite POVM: $E_b\ge0$ and $\sum_bE_b=I$. Define
--   $$V\psi=\sum_b\sqrt{E_b}\psi\otimes|b\rangle,\qquad F_b=I\otimes|b\rangle\langle b|.$$
--   Then $V^{\dagger}V=I$, the $F_b$ sum to the identity and satisfy $F_bF_c=\delta_{bc}F_b$, and for every density matrix $\rho$,
--   $$\operatorname{Tr}[F_bV\rho V^{\dagger}]=\operatorname{Tr}(E_b\rho).$$
--   This is the computed projective dilation of the specified POVM; effects may be singular.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 11, Section 3.5: computed projective representation of a POVM

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

/-- Section 3.5, PDF p.11: the computed Naimark representation, with unchanged
outcome probabilities and genuinely projective enlarged effects. -/
theorem naimark [Nonempty A] [Nonempty O] (E : O → Mat A) (hE : IsPOVM E) :
    let V := krausV (fun b => cfc Real.sqrt (E b))
    Vᴴ * V = 1 ∧ IsPOVM (coordinatePVM (A := A) (O := O)) ∧
    (∀ b c : O, coordinatePVM (A := A) b * coordinatePVM c =
      if b = c then coordinatePVM b else 0) ∧
    (∀ rho : Mat A, IsDensityMatrix rho → ∀ b,
      effectProb (coordinatePVM b) (V * rho * Vᴴ) = effectProb (E b) rho) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
