-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_pureDistance
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.pureDistance
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:16:29.111007+00:00
-- url     : https://prove2.me/theorems/bef248a8-4bda-47af-bd31-406dc92ec6d1
-- title:
--   Lemma I.2: For normalized pure rho,sigma: 1−Tr(rho sigma)=(traceNorm(rho−sigma)/2)².
-- statement:
--   Let $\rho,\sigma$ be normalized pure states on one finite system. Write $D(\rho,\sigma)=\|\rho-\sigma\|_1/2$.
--
--   $$
--   1-\operatorname{Tr}(\rho\sigma)=D(\rho,\sigma)^2.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 8, Lemma I.2

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

/-- Lemma I.2, PDF p.8: pure-state overlap and half trace distance. -/
theorem pureDistance {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (hrho : IsPure rho) (hsigma : IsPure sigma) :
    1 - effectProb rho sigma = (traceDistance rho sigma)^2 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
