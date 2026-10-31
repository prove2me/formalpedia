-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_renyi_spectrum_representations
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.renyi_spectrum_representations
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:47:59.795728+00:00
-- url     : https://prove2.me/theorems/79ef2d74-9e26-4346-8c35-a442e2f35a09
-- title:
--   Theorem 35: All four representations (471)–(474) of Renyi divergence in terms of zeta_alpha(beta)=beta^(alpha-2)(1-F(log beta))
-- statement:
--   Let $P\ll Q$, $\alpha>0$, $\alpha\ne1$, $F(t)=F_{P\|Q}(\log_b t)$, and $\zeta(t)=t^{\alpha-2}(1-F(t))$. Then $(\alpha-1)D_\alpha$ is the base-$b$ logarithm of each applicable expression:
--
--   $$\begin{cases}
--   \beta_1^{1-\alpha}+(1-\alpha)\int_{\beta_2}^{\beta_1^{-1}}t^{\alpha-2}F(t)dt&\beta_1>0,\\
--   (1-\alpha)\int_{\beta_2}^\infty t^{\alpha-2}F(t)dt&\beta_1=0,\ \alpha<1,\\
--   (\alpha-1)\int_0^\infty\zeta(t)dt&\alpha>1,\\
--   \beta_2^{\alpha-1}+(\alpha-1)\int_{\beta_2}^\infty\zeta(t)dt&\alpha>1.
--   \end{cases}$$
--
--   The pointwise identity $t^{\alpha-2}-\zeta=t^{\alpha-2}F$ avoids subtracting infinite integrals. All four formulas (471)–(474), including $P=Q$, are retained.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 66, Theorem 35

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 35: All four representations (471)–(474) of Renyi divergence in terms of zeta_alpha(inverseUpperDensity)=inverseUpperDensity^(alpha-2)(1-F(log inverseUpperDensity)). Sason--Verdu, arXiv:1508.00335v7, PDF p.66.  -/
theorem renyi_spectrum_representations
    (b : LogBase) (a : ℝ) (ha : 0 < a ∧ a ≠ 1)
    {A : Type u} [MeasurableSpace A] (P Q : Measure A)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    (0 < inverseUpperDensity P Q → renyiDiv b a P Q = ((1 / (a - 1) : ℝ) : EReal) *
      elogB b (((Real.rpow (inverseUpperDensity P Q) (1 - a) : EReal) +
        ((1 - a : ℝ) : EReal) * (cdfMoment b a P Q (ENNReal.ofReal (inverseUpperDensity Q P))
          (upperDensity P Q) : EReal)).toENNReal)) ∧
    (inverseUpperDensity P Q = 0 → a < 1 → renyiDiv b a P Q = ((1 / (a - 1) : ℝ) : EReal) *
      elogB b (ENNReal.ofReal (1 - a) * cdfMoment b a P Q (ENNReal.ofReal (inverseUpperDensity Q P)) ∞)) ∧
    (1 < a → renyiDiv b a P Q = ((1 / (a - 1) : ℝ) : EReal) *
      elogB b (ENNReal.ofReal (a - 1) * tailMoment b a P Q 0 ∞) ∧
      renyiDiv b a P Q = ((1 / (a - 1) : ℝ) : EReal) *
      elogB b ((ENNReal.ofReal (inverseUpperDensity Q P)) ^ (a - 1) +
        ENNReal.ofReal (a - 1) * tailMoment b a P Q (ENNReal.ofReal (inverseUpperDensity Q P)) ∞)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
