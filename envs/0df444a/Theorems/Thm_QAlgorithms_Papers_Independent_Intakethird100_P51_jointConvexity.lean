-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_jointConvexity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.jointConvexity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:56:46.902584+00:00
-- url     : https://prove2.me/theorems/19664f58-9e01-406a-991e-c86ab83be34c
-- title:
--   Theorem 7: joint convexity with equality
-- statement:
--   Let $\lambda_k>0$ be finitely many weights summing to one, and let $\rho_k,\gamma_k>0$ be positive definite matrices of a common size. Define $\rho=\sum_k\lambda_k\rho_k$ and $\gamma=\sum_k\lambda_k\gamma_k$. Then
--   $$H(\rho,\gamma)\le\sum_k\lambda_kH(\rho_k,\gamma_k),$$
--   with equality if and only if $\log\rho-\log\gamma=\log\rho_k-\log\gamma_k$ for every $k$. No trace-one or equal-trace hypothesis is imposed. This is the full cone version of joint convexity and its equality criterion.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 14, Theorem 7: joint convexity with equality

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

/-- Theorem 7, PDF p.14: joint convexity and equality for positive weights and
positive definite pairs. Neither equal trace nor trace one is assumed. -/
theorem jointConvexity [Nonempty A] [Nonempty J] (w : J → ℝ) (hw : ∀ j, 0 < w j) (hs : ∑ j, w j = 1)
    (rho gamma : J → Mat A) (hr : ∀ j, (rho j).PosDef) (hg : ∀ j, (gamma j).PosDef) :
    (relativeEntropy (average w rho) (average w gamma)).toReal ≤ ∑ j, w j * (relativeEntropy (rho j) (gamma j)).toReal ∧
      ((relativeEntropy (average w rho) (average w gamma)).toReal =
        ∑ j, w j * (relativeEntropy (rho j) (gamma j)).toReal ↔
        ∀ j, logMatrix (average w rho) - logMatrix (average w gamma) =
          logMatrix (rho j) - logMatrix (gamma j)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
