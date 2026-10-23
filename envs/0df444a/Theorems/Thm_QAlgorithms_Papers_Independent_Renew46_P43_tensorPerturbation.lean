-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_tensorPerturbation
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.tensorPerturbation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T07:12:05.521325+00:00
-- url     : https://prove2.me/theorems/d6c71b69-79fd-43fb-ae53-c57ae8c7fd70
-- title:
--   tensor-distance-fidelity: Trace-norm tensor perturbation≤sum of factor perturbations; overlap infidelity of tensor products≤sum of factor overlap infideliti
-- statement:
--   Let $\rho_1,\sigma_1$ be normalized states on one finite system and $\rho_2,\sigma_2$ normalized states on another. The norm is the unhalved trace norm and the fidelity is overlap $\operatorname{Tr}(\rho\sigma)$.
--
--   $$
--   \|\rho_1\otimes\rho_2-\sigma_1\otimes\sigma_2\|_1\le\|\rho_1-\sigma_1\|_1+\|\rho_2-\sigma_2\|_1,\quad1-\operatorname{Tr}((\rho_1\otimes\rho_2)(\sigma_1\otimes\sigma_2))\le\sum_{i=1}^2(1-\operatorname{Tr}(\rho_i\sigma_i)).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 8, tensor-distance-fidelity

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

/-- Unnumbered tensor inequalities, PDF p.8. All four factors are normalized. -/
theorem tensorPerturbation {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (rho1 sigma1 : Matrix I I ℂ) (rho2 sigma2 : Matrix J J ℂ)
    (hrho1 : IsDensityMatrix rho1) (hsigma1 : IsDensityMatrix sigma1)
    (hrho2 : IsDensityMatrix rho2) (hsigma2 : IsDensityMatrix sigma2) :
    traceNorm (Matrix.kronecker rho1 rho2 - Matrix.kronecker sigma1 sigma2) ≤
      traceNorm (rho1 - sigma1) + traceNorm (rho2 - sigma2) ∧
    1 - effectProb (Matrix.kronecker rho1 rho2) (Matrix.kronecker sigma1 sigma2) ≤
      (1 - effectProb rho1 sigma1) + (1 - effectProb rho2 sigma2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
