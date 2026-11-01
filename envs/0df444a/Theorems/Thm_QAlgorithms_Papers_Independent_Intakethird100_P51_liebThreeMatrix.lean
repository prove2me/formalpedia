-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_liebThreeMatrix
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.liebThreeMatrix
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:46:36.812586+00:00
-- url     : https://prove2.me/theorems/d5ce4dfa-a83d-403e-a9cf-ae247fb86d34
-- title:
--   Theorem 5: Lieb three-matrix resolvent trace inequality
-- statement:
--   Let $R,S,T>0$ be positive definite matrices. The matrix-valued function $u\mapsto R(S+uI)^{-1}T(S+uI)^{-1}$ is integrable on $[0,\infty)$, and
--   $$\operatorname{Tr}e^{\log R-\log S+\log T}\le\operatorname{Tr}\int_0^\infty R(S+uI)^{-1}T(S+uI)^{-1}\,du.$$
--   Pairwise commutation of $R,S,T$ is sufficient for equality. It is not asserted necessary. This is Lieb’s three-matrix bound used in the proof of SSA.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 9, Theorem 5: Lieb three-matrix resolvent trace inequality

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

/-- Theorem 5, equation (17), PDF p.9: the factor R is inside the integral.
Integrability is a conclusion. Commutation is sufficient for equality, not necessary. -/
theorem liebThreeMatrix [Nonempty A] (R S T : Mat A) (hR : R.PosDef) (hS : S.PosDef) (hT : T.PosDef) :
    IntegrableOn (fun u : ℝ => R * (S + (u : ℂ) • 1)⁻¹ * T * (S + (u : ℂ) • 1)⁻¹)
      (Set.Ici 0) ∧
    (NormedSpace.exp (logMatrix R - logMatrix S + logMatrix T)).trace.re ≤
      (∫ u : ℝ in Set.Ici 0, R * (S + (u : ℂ) • 1)⁻¹ * T * (S + (u : ℂ) • 1)⁻¹).trace.re ∧
    ((R * S = S * R ∧ R * T = T * R ∧ S * T = T * S) →
      (NormedSpace.exp (logMatrix R - logMatrix S + logMatrix T)).trace.re =
        (∫ u : ℝ in Set.Ici 0, R * (S + (u : ℂ) • 1)⁻¹ * T * (S + (u : ℂ) • 1)⁻¹).trace.re) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
