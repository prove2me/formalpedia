-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_finite_kl_chi_lower
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.finite_kl_chi_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:54:57.47378+00:00
-- url     : https://prove2.me/theorems/c781257a-ef18-4b7d-9f76-82f7e846a77e
-- title:
--   Remark 34: finite-alphabet entropy/chi-square lower bound (375)
-- statement:
--   For distinct probability laws on a common finite alphabet of more than one symbol, with $Q$ strictly positive,
--
--   $$\frac{D(P\|Q)}{\chi^2(P\|Q)}\ge Q_{\min}\log_b e.$$
--
--   The denominator is finite and positive. No optimality claim for this coefficient is added.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 51, Remark 34

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Remark 34: finite-alphabet shannonEntropyBase/chiSquareDiv-square lower bound (375). Sason--Verdu, arXiv:1508.00335v7, PDF p.51.  -/
theorem finite_kl_chi_lower
    (b : LogBase) (n : ℕ) (hn : 1 < n) (p q : Fin n → ℝ)
    (hp : FiniteProbabilityLaw p) (hq : FiniteProbabilityLaw q) (hqpos : ∀ i, 0 < q i) (hne : p ≠ q) :
    minReferenceMass q * logBaseE b ≤ finiteKL b p q / finiteChi p q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
