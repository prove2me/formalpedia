-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_tenderOperator
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.tenderOperator
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:17:59.225551+00:00
-- url     : https://prove2.me/theorems/07643006-2399-4fc5-9dbf-907e02076064
-- title:
--   Lemma I.4: For state rho, 0≤X≤I and 1−Tr(rho X)≤lambda≤1, ||rho−sqrt(X)rho sqrt(X)||1≤sqrt(8lambda).
-- statement:
--   Let $\rho$ be a normalized state and $0\le X\le1$. Assume $1-\operatorname{Tr}(\rho X)\le\lambda\le1$; nonnegativity of $\lambda$ follows from these assumptions.
--
--   $$
--   \left\|\rho-\sqrt X\rho\sqrt X\right\|_1\le\sqrt{8\lambda}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 9, Lemma I.4

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

/-- Lemma I.4, PDF p.9: unhalved norm and sqrt(8 lambda). -/
theorem tenderOperator {I : Type*} [Fintype I] [DecidableEq I]
    (rho X : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hX : IsEffect X)
    (lambda : ℝ) (herror : 1 - effectProb rho X ≤ lambda) (hlambda : lambda ≤ 1) :
    traceNorm (rho - cfc Real.sqrt X * rho * cfc Real.sqrt X) ≤ Real.sqrt (8 * lambda) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
