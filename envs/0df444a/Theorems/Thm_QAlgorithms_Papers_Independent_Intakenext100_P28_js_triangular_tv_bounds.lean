-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_js_triangular_tv_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.js_triangular_tv_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:33:28.740435+00:00
-- url     : https://prove2.me/theorems/50c88da9-b5fc-4428-8a5a-929e24440456
-- title:
--   Theorem 10: (log e)/2<=JS/Delta<=max{kappa1(beta1^{-1}),kappa1(beta2)} and Delta/TV<=max{kappa2(beta1^{-1}),kappa2(beta2)}
-- statement:
--   For distinct probability measures $P\ll Q$ with betas below 1,
--
--   $$\frac{\log_b e}{2}\Delta\le JS\le
--   \max\{\kappa_1(\beta_1^{-1}),\kappa_1(\beta_2)\}\Delta,
--   \qquad\Delta\le\max\{\kappa_2(\beta_1^{-1}),\kappa_2(\beta_2)\}|P-Q|.$$
--
--   Here $\kappa_1(t)=(t+1)[t\log_b t-(t+1)\log_b((t+1)/2)]/(t-1)^2$, with endpoint values $\log_b2$ at 0 and infinity and $(\log_b e)/2$ at 1; $\kappa_2(t)=|t-1|/(t+1)$, with value 1 at infinity. These give the complete (185)–(188).
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 28, Theorem 10

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 10: (log e)/2<=JS/Delta<=max{kappa1(beta1^{-1}),kappa1(beta2)} and Delta/TV<=max{kappa2(beta1^{-1}),kappa2(beta2)}. Sason--Verdu, arXiv:1508.00335v7, PDF p.28.  -/
theorem js_triangular_tv_bounds
    (b : LogBase) {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) (hne : P ≠ Q)
    (hb1 : inverseUpperDensity P Q < 1) (hb2 : inverseUpperDensity Q P < 1) :
    ENNReal.ofReal (logBaseE b / 2) * triangular P Q ≤ js b P Q ∧
    js b P Q ≤ max (jsTriangularKernel b (upperDensity P Q))
      (jsTriangularKernel b (ENNReal.ofReal (inverseUpperDensity Q P))) * triangular P Q ∧
    triangular P Q ≤ max (triangularTVKernel (upperDensity P Q))
      (triangularTVKernel (ENNReal.ofReal (inverseUpperDensity Q P))) * fullVariation P Q := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
