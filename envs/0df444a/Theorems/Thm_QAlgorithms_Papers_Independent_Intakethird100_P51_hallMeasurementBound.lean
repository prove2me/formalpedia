-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_hallMeasurementBound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.hallMeasurementBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:04:34.381046+00:00
-- url     : https://prove2.me/theorems/05051c22-8906-471d-9e75-9b1ea37edeaf
-- title:
--   Equations (59),(60): Hall alternative accessible-information bound
-- statement:
--   For any finite normalized PSD ensemble $\mathcal E$ with average $\rho$ and any finite POVM $\mathcal M=\{E_b\}$, set $\tau_b=\operatorname{Tr}(E_b\rho)$ and, only when $\tau_b>0$, $\sigma_b=\tau_b^{-1}\sqrt\rho E_b\sqrt\rho$. Then
--   $$I(\mathcal E,\mathcal M)\le S(\rho)-\sum_{b:\tau_b>0}\tau_bS(\sigma_b)=\sum_{b:\tau_b>0}\tau_bH(\sigma_b,\rho).$$
--   The average may be singular; the active dual states are supported on its support. This is Hall’s alternative bound, with the probability factor retained in both sums.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 21, Equations (59),(60): Hall alternative accessible-information bound

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

/-- Section 7.4, equations (59)–(60), PDF p.21: Hall's bound with the tau_b
factor and only active normalization. The average may be singular. -/
theorem hallMeasurementBound [Nonempty A] [Nonempty J] [Nonempty O] (w : J → ℝ) (hw : IsLaw w)
    (sigma : J → Mat A) (hs : ∀ j, IsDensityMatrix (sigma j)) (E : O → Mat A) (hE : IsPOVM E) :
    (Real.log 2 * measurementInformation w sigma E) ≤ hallBound (average w sigma) E ∧
      hallBound (average w sigma) E = hallRelative (average w sigma) E := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
