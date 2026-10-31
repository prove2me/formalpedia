-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_entropy_hellinger_kernel_monotone
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.entropy_hellinger_kernel_monotone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:44:39.713704+00:00
-- url     : https://prove2.me/theorems/7b825aae-dc9d-46a7-be87-0c8b1261da02
-- title:
--   Appendix B: monotonicity of the kernel (176)
-- statement:
--   For $\alpha>0$, $\alpha\ne1$, the continuous extended kernel $\kappa_\alpha$ of (176) satisfies
--
--   $$\alpha<1\implies\kappa_\alpha\text{ is increasing on }[0,\infty],\qquad
--   \alpha>1\implies\kappa_\alpha\text{ is decreasing on }[0,\infty].$$
--
--   The endpoint values at 0,1,infinity are included. This is the auxiliary result explicitly stated at the opening of Appendix B.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 75, Appendix B

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Appendix B: monotonicity of the kernel (176). Sason--Verdu, arXiv:1508.00335v7, PDF p.75.  -/
theorem entropy_hellinger_kernel_monotone
    (b : LogBase) (a : ℝ) (ha : 0 < a ∧ a ≠ 1) :
    (a < 1 → Monotone (entropyHellingerKernel b a)) ∧
    (1 < a → Antitone (entropyHellingerKernel b a)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
