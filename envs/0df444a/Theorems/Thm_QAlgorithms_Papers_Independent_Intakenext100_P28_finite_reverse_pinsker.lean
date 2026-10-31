-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_finite_reverse_pinsker
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.finite_reverse_pinsker
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:52:47.17821+00:00
-- url     : https://prove2.me/theorems/1d7f4a8c-849b-4f15-98af-0d85011e005d
-- title:
--   Theorem 28: Finite alphabet: D<=log(1+TV^2/(2Qmin)); if Q≪P subtract beta2 TV^2 log e/2 for the tightened bound
-- statement:
--   On a finite alphabet of size greater than 1, let $Q$ be strictly positive and $Q_{\min}=\min_iQ(i)$. Then
--
--   $$D(P\|Q)\le\log_b\left(1+\frac{|P-Q|^2}{2Q_{\min}}\right).$$
--
--   If also $Q\ll P$, the upper bound tightens by subtracting $\beta_2|P-Q|^2\log_b e/2$, where $\beta_2=\min_iP(i)/Q(i)$. The additional reverse-AC condition belongs only to the tightened bound.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 50, Theorem 28

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 28: Finite alphabet: D<=log(1+TV^2/(2Qmin)); if Q≪P subtract beta2 TV^2 log e/2 for the tightened bound. Sason--Verdu, arXiv:1508.00335v7, PDF p.50.  -/
theorem finite_reverse_pinsker
    (b : LogBase) (n : ℕ) (hn : 1 < n) (p q : Fin n → ℝ)
    (hp : FiniteProbabilityLaw p) (hq : FiniteProbabilityLaw q) (hqpos : ∀ i, 0 < q i) :
    finiteKL b p q ≤ logB b (1 + finiteTV p q ^ 2 / (2 * minReferenceMass q)) ∧
    ((∀ i, 0 < p i) → finiteKL b p q ≤ logB b (1 + finiteTV p q ^ 2 / (2 * minReferenceMass q)) -
      finiteBeta2 p q * logBaseE b / 2 * finiteTV p q ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
