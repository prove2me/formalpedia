-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_finite_l2_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.finite_l2_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:54:36.559641+00:00
-- url     : https://prove2.me/theorems/d7fac57f-14de-43bb-8057-ed494a08b995
-- title:
--   Remark 33: tightened finite-alphabet l2 bound (374)
-- statement:
--   For finite probability laws on more than one symbol, with strictly positive $Q$ and unweighted squared norm $\|P-Q\|_2^2=\sum_i(P(i)-Q(i))^2$,
--
--   $$D(P\|Q)\le\|P-Q\|_2^2\log_b e/Q_{\min}.$$
--
--   If also $Q\ll P$, then $D(P\|Q)\le\log_b(1+\|P-Q\|_2^2/Q_{\min})-\beta_2\|P-Q\|_2^2\log_b e/2$. The first bound is cited background (373); the refinement is (374).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 51, Remark 33

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Remark 33: tightened finite-alphabet l2 bound (374). Sason--Verdu, arXiv:1508.00335v7, PDF p.51.  -/
theorem finite_l2_bounds
    (b : LogBase) (n : ℕ) (hn : 1 < n) (p q : Fin n → ℝ)
    (hp : FiniteProbabilityLaw p) (hq : FiniteProbabilityLaw q) (hqpos : ∀ i, 0 < q i) :
    finiteKL b p q ≤ finiteL2 p q * logBaseE b / minReferenceMass q ∧
    ((∀ i, 0 < p i) → finiteKL b p q ≤ logB b (1 + finiteL2 p q / minReferenceMass q) -
      finiteBeta2 p q * logBaseE b / 2 * finiteL2 p q) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
