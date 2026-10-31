-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_samson
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.samson
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:29:39.605071+00:00
-- url     : https://prove2.me/theorems/fa136166-9213-4603-a7a0-a7584789674c
-- title:
--   Theorem 4: Samson inequality: d2sq(P,Q)+d2sq(Q,P)<=(2/log e)D(P||Q)
-- statement:
--   Let $P\ll Q$ be probability measures on a common arbitrary measurable alphabet. Marton's squared divergence $d_2^2$ satisfies
--
--   $$d_2^2(P,Q)+d_2^2(Q,P)\le\frac{2}{\log_b e}D(P\|Q).$$
--
--   This is Samson's inequality, attributed in the paper to Samson [89, Lemma 2]. The coefficient is $2/(\log_b e)$.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 20, Theorem 4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 4: Samson inequality: d2sq(P,Q)+d2sq(Q,P)<=(2/log e)D(P||Q). Sason--Verdu, arXiv:1508.00335v7, PDF p.20.  -/
theorem samson
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    martonSum P Q ≤ ENNReal.ofReal (2 / logBaseE b) * kl b P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
