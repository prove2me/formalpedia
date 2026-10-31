-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_cGamma_limits
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.cGamma_limits
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:52:06.552513+00:00
-- url     : https://prove2.me/theorems/34c9f4ec-06d0-4e25-994b-eff12ce994e7
-- title:
--   Remarks 42–44: no reverse KL control, monotonicity and singular limit
-- statement:
--   The exact coefficient $c_\gamma$ is decreasing for $\gamma>1$ and
--
--   $$\lim_{\gamma\downarrow1}c_\gamma=+\infty.$$
--
--   For every $\gamma>1$, the binary pair $P(0)=(1+\gamma)/(2\gamma)$, $Q(0)=1/\gamma$ has $P\ll Q$, $P\ne Q$, $0<D(P\|Q)<\infty$, but $E_\gamma(P\|Q)=0$. Hence no positive universal multiple of KL lower-bounds $E_\gamma$. This is the comparison-class interpretation of Remark 42, together with Remarks 43–44.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 64, Remarks 42–44

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Remarks 42–44: no reverse KL control, monotonicity and singular limit. Sason--Verdu, arXiv:1508.00335v7, PDF p.64.  -/
theorem cGamma_limits
    (b : LogBase) :
    AntitoneOn (hockeyKLConstant b) (Ioi 1) ∧
    Tendsto (hockeyKLConstant b) (nhdsWithin 1 (Ioi 1)) atTop ∧
    (∀ g : ℝ, 1 < g → let P := binary ((1 + g) / (2 * g))
      let Q := binary g⁻¹
      IsProbabilityMeasure P ∧ IsProbabilityMeasure Q ∧ P ≪ Q ∧ P ≠ Q ∧
      hockey g P Q = 0 ∧ 0 < kl b P Q ∧ kl b P Q < ∞) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
