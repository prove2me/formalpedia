-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_rateSlicing
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.rateSlicing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:50:39.502141+00:00
-- url     : https://prove2.me/theorems/cdccbfd1-5736-4b1b-b191-47d87baf755f
-- title:
--   Theorem IV.11: For c1h1 source, lambdaBar,delta>0 and all sufficiently large n, a side-information code has log2|M|/n≤H(X|Y)+3delta and mean erro
-- statement:
--   For a finite correlated classical/hybrid source $(X,Y)$ and $\bar\lambda,\delta>0$, all sufficiently large positive block lengths admit a classical encoding $f:X^n\to M$ and a conditioned collective POVM on the free register $Y^n$. Its square-root instrument retains the decoded word and $Y^n$, then discards the transmitted classical message; it also retains a failure outcome.
--
--   $$
--   \frac1n\log_2|M|\le H(X\mid Y)+3\delta,\quad\bar e\le\bar\lambda,\quad\mathbb E\|[x^n]\otimes\pi^n-D'_*( [f(x^n)]\otimes\pi^n)\|_1\le\sqrt{8\bar\lambda}+\bar\lambda.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 53, Theorem IV.11

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

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Theorem IV.11, PDF pp.53-54: rate slicing with the actual retained-outcome
square-root instrument. Printed epsilon-bar in the threshold is corrected to lambda-bar,
and the omitted n-th powers are restored from the n-block definition. -/
theorem rateSlicing (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (lambda delta : ℝ) (hlambda : 0 < lambda) (hdelta : 0 < delta) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ (S : HybridSource 1),
      (∀ i, S.alphabet i = a) → S.system.dim = d → ∀ n : ℕ, n0 ≤ n →
      ∃ c : SideCode S n, c.rate 0 ≤ S.subsetEntropy Finset.univ + 3 * delta ∧
        c.error ≤ lambda ∧ c.disturbance ≤ Real.sqrt (8 * lambda) + lambda := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
