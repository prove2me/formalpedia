-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_moment_kl_refinement
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.moment_kl_refinement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:38:49.271668+00:00
-- url     : https://prove2.me/theorems/c849bfe3-de39-45df-92b6-9678f98d578a
-- title:
--   Theorem 23: With c=chi2(P||Q),d=chi2(Q||P), D<=log(1+c)-[(3/2)c^2 log e]/[(1+d)(1+c)^2-1]
-- statement:
--   Let $P,Q$ be mutually absolutely continuous probability measures, and put $c=\chi^2(P\|Q)$, $d=\chi^2(Q\|P)$. Then
--
--   $$D(P\|Q)\le\log_b(1+c)-\frac{(3/2)c^2\log_b e}{(1+d)(1+c)^2-1}.$$
--
--   At $c=d=0$ the right side is 0; if $c=\infty$ it is infinity; if $c<\infty$ and $d=\infty$, the correction is 0. These explicit limiting cases avoid a totalized $0/0$ or infinity subtraction. The separately inventoried asymptotic clause is deferred.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 41, Theorem 23

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 23: With c=chi2(P||Q),d=chi2(Q||P), D<=log(1+c)-[(3/2)c^2 log e]/[(1+d)(1+c)^2-1]. Sason--Verdu, arXiv:1508.00335v7, PDF p.41.  -/
theorem moment_kl_refinement
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    (kl b P Q : EReal) ≤ momentKLBound b (chiSquareDiv P Q) (chiSquareDiv Q P) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
