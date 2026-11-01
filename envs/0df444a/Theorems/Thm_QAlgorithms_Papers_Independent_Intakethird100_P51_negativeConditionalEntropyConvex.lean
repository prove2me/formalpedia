-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_negativeConditionalEntropyConvex
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.negativeConditionalEntropyConvex
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:57:27.87979+00:00
-- url     : https://prove2.me/theorems/fe60c8ff-7a13-4dfa-94c0-0a3f4f7c7e88
-- title:
--   Section 5.3: convexity of negative conditional entropy
-- statement:
--   Let $\lambda_k\ge0$ sum to one and let $\rho^{(k)}_{12}$ be finite normalized PSD states, with $\rho_{12}=\sum_k\lambda_k\rho^{(k)}_{12}$. Then
--   $$S(\rho_1)-S(\rho_{12})\le\sum_k\lambda_k\bigl[S(\rho^{(k)}_1)-S(\rho^{(k)}_{12})\bigr].$$
--   The marginal index is $1$, and all marginal states are partial traces. This is convexity of negative conditional entropy of system $2$ conditioned on $1$, including singular states.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 15, Section 5.3: convexity of negative conditional entropy

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

/-- Section 5.3, PDF pp.14–15: convexity of S(rho1)-S(rho12); the marginal is 1.
PSD block states are allowed. -/
theorem negativeConditionalEntropyConvex [Nonempty A] [Nonempty B] [Nonempty J] (w : J → ℝ) (hw : IsLaw w)
    (rho : J → Mat (A × B)) (hr : ∀ j, IsDensityMatrix (rho j)) :
    entropy (traceRight (average w rho)) - entropy (average w rho) ≤
      ∑ j, w j * (entropy (traceRight (rho j)) - entropy (rho j)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
