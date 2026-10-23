-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_mixedDistance
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.mixedDistance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:17:09.66986+00:00
-- url     : https://prove2.me/theorems/e72e3f0e-d6a9-452e-aa75-25431e2f4dee
-- title:
--   Lemma I.3: For pure rho and normalized arbitrary sigma: D²≤1−F≤D.
-- statement:
--   Let $\rho$ be a normalized pure state and $\sigma$ any normalized density operator on the same finite system. Write $D(\rho,\sigma)=\|\rho-\sigma\|_1/2$.
--
--   $$
--   D(\rho,\sigma)\ge 1-\operatorname{Tr}(\rho\sigma)\ge D(\rho,\sigma)^2.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 9, Lemma I.3

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma I.3, PDF p.9. Both states are normalized; the printed subnormalized
extension is false and is separately recorded in HARD.md. -/
theorem mixedDistance {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : IsPure rho) (hsigma : IsDensityMatrix sigma) :
    traceDistance rho sigma ≥ 1 - effectProb rho sigma ∧
      1 - effectProb rho sigma ≥ (traceDistance rho sigma)^2 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
