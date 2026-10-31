-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_entropy_kernel_strictMono
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.entropy_kernel_strictMono
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:42:04.720654+00:00
-- url     : https://prove2.me/theorems/19196d31-8aa3-4620-8bbd-7be0fb085601
-- title:
--   Lemma 2: The continuous extension of kappa(t)=r(t)/[(t-1)log e-log t], kappa(1)=1, is strictly increasing on (0,infinity)
-- statement:
--   Let $r(t)=t\log_b t+(1-t)\log_b e$. The continuous extension at 1 of
--
--   $$\kappa(t)=\frac{r(t)}{(t-1)\log_b e-\log_b t},\qquad\kappa(1)=1,$$
--
--   is strictly increasing on $(0,\infty)$. The explicit value at 1 avoids a totalized zero quotient.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 74, Lemma 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Lemma 2: The continuous extension of kappa(t)=r(t)/[(t-1)log e-log t], kappa(1)=1, is strictly increasing on (0,infinity). Sason--Verdu, arXiv:1508.00335v7, PDF p.74.  -/
theorem entropy_kernel_strictMono
    (b : LogBase) : StrictMonoOn (entropyKernel b) (Ioi 0) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
