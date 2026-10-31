-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P61_conditionalMean_lower_tail
-- name    : QAlgorithms.Papers.Independent.Intake100.P61.conditionalMean_lower_tail
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:04:57.468862+00:00
-- url     : https://prove2.me/theorems/edb7a42a-0d81-4fc0-bb8f-af5222f16818
-- title:
--   Lemma 11: conditional-mean lower tail from a joint lower tail
-- statement:
--   Let $(X,Y)$ have a measurable nonnegative probability density $p$ on $[0,\infty)^2$, and let $m(x)=\int_0^\infty y\,p(y\mid x)\,dy$ be its actual extended conditional mean, with arbitrary zero values on null marginal fibers. For $a,b\ge0$ and $\delta>0$, suppose $\Pr[X\ge a,Y\le b]\le\eta$ for a nonnegative extended bound $\eta$. Then
--
--   $$\Pr[X\ge a,\ m(X)\le b-\delta]\le\frac{b\eta}{\delta}.$$
--
--   A negative real threshold $b-\delta$ makes the event empty. In Lean this is expressed by including $\delta\le b$ inside the event before converting its threshold to an extended nonnegative real. The result concerns nonnegative variables and does not bound arbitrary signed correlations.
-- source:
--   Composable security proof for continuous-variable quantum key distribution with coherent states, arXiv:1408.5689v3, PDF p. 23, Lemma 11, E28–E34

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P61

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P61

attribute [local instance] Classical.propDecidable Classical.decEq

-- The frozen frequency formula specializes exactly to the source alphabet Fin (2 ^ d).

open QAlgorithms.Papers.Independent.Advance50.P30 (empiricalFrequency)

/-- PDF p.23, Lemma 11 (E28–E34): epsilon_2 denotes a tail bound, not a square.
The delta<=b clause in the event expresses that a nonnegative conditional mean
cannot be <= a negative real threshold; it does not restrict the theorem's domain. -/
theorem conditionalMean_lower_tail
    (p : ℝ × ℝ → ℝ≥0∞) (hp : Measurable p) [IsProbabilityMeasure (quadrantLaw p)]
    (a b delta : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hdelta : 0 < delta)
    (eta : ℝ≥0∞) (htail : quadrantLaw p {v | a ≤ v.1 ∧ v.2 ≤ b} ≤ eta) :
    quadrantLaw p {v | a ≤ v.1 ∧ delta ≤ b ∧
      densityConditionalMean p v.1 ≤ ENNReal.ofReal (b - delta)} ≤
      ENNReal.ofReal b * eta / ENNReal.ofReal delta := by sorry

end QAlgorithms.Papers.Independent.Intake100.P61

end
