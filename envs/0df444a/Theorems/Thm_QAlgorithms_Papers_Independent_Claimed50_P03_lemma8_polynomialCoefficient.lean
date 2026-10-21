-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P03_lemma8_polynomialCoefficient
-- name    : QAlgorithms.Papers.Independent.Claimed50.P03.lemma8_polynomialCoefficient
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:04:25.511761+00:00
-- url     : https://prove2.me/theorems/c6c517d6-9b7a-42b6-a3bf-24633b34856f
-- title:
--   Lemma 8 (Polynomial coefficient bound)
-- statement:
--   Let $p(t)=\sum_{i=1}^k a_i t^i$ have real coefficients, and let $1\le j\le k$. Then there exists $t\in[-1,1]$ such that
--   $$|a_j|\le(1+\sqrt2)^k|p(t)|.$$
--   A continuous polynomial attains its maximum absolute value on this compact interval, so this is equivalent to the printed bound by $\sup_{|t|\le1}|p(t)|$. No attainment hypothesis is assumed.
-- source:
--   Learning to predict arbitrary quantum processes, arXiv:2210.14894v3, PDF p. 30, Lemma 8 (Polynomial coefficient bound)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P03

open MeasureTheory

attribute [local instance] Classical.propDecidable

open scoped BigOperators ComplexConjugate

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P03.namedWireMatrixBorelSpace

/-- Paper p.30, A90: coefficient bound for a real polynomial with no constant
term. The supremum on [-1,1] is attained; expressing it by an existential
point preserves its value without a totalized real supremum. -/
theorem lemma8_polynomialCoefficient (k : ℕ) (a : ℕ → ℝ) (j : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      |a j| ≤ (1 + Real.sqrt 2) ^ k * |∑ i ∈ Finset.Icc 1 k, a i * t ^ i| := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P03

end
