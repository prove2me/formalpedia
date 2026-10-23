-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_shadowBound
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.shadowBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:23:26.628143+00:00
-- url     : https://prove2.me/theorems/2dba692c-7dbd-4d59-88f3-8427cfa6e693
-- title:
--   Lemma I.10: Under the printed positive contraction and sandwich hypotheses: (1−lambda)/mu2≤Tr Lambda≤1/mu1; eta-shadow trace≥(eta−sqrt(8lambda
-- statement:
--   Let $\rho$ be a normalized state, $0\le\Lambda\le1$, and $\lambda,\mu_1,\mu_2>0$. Assume $\operatorname{Tr}(\rho\Lambda)\ge1-\lambda$ and $\mu_1\Lambda\le\sqrt\Lambda\rho\sqrt\Lambda\le\mu_2\Lambda$. Let $0\le B\le1$ have $\operatorname{Tr}(\rho B)\ge\eta$.
--
--   $$
--   \frac{1-\lambda}{\mu_2}\le\operatorname{Tr}\Lambda\le\frac1{\mu_1},\quad\operatorname{Tr}B\ge\frac{\eta-\sqrt{8\lambda}}{\mu_2},\quad[\rho,\Lambda]=0\Longrightarrow\operatorname{Tr}B\ge\frac{\eta-\lambda}{\mu_2}.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 13, Lemma I.10

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

/-- Lemma I.10, PDF p.13: the lower trace bound divides by mu2, upper by mu1.
The last clause applies when rho and Lambda commute. -/
theorem shadowBound {I : Type} [Fintype I] [DecidableEq I]
    (rho L : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hL : IsEffect L)
    (lambda mu1 mu2 : ℝ) (hlambda : 0 < lambda) (hmu1 : 0 < mu1) (hmu2 : 0 < mu2)
    (hweight : effectProb rho L ≥ 1 - lambda)
    (hlower : Below ((mu1 : ℂ) • L) (cfc Real.sqrt L * rho * cfc Real.sqrt L))
    (hupper : Below (cfc Real.sqrt L * rho * cfc Real.sqrt L) ((mu2 : ℂ) • L)) :
    (1 - lambda) / mu2 ≤ L.trace.re ∧ L.trace.re ≤ 1 / mu1 ∧
    ∀ (B : Matrix I I ℂ) (eta : ℝ), IsShadow rho B eta →
      B.trace.re ≥ (eta - Real.sqrt (8 * lambda)) / mu2 ∧
      (rho * L = L * rho → B.trace.re ≥ (eta - lambda) / mu2) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
