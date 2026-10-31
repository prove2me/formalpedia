-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P61_conditionalMean_upper_tail
-- name    : QAlgorithms.Papers.Independent.Intake100.P61.conditionalMean_upper_tail
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:04:07.292978+00:00
-- url     : https://prove2.me/theorems/10df8b5c-b7f2-4805-9346-28f6e60833c5
-- title:
--   Lemma 10: conditional-mean upper tail from joint-tail bounds
-- statement:
--   Let $(X,Y)$ have a measurable nonnegative probability density $p$ on $[0,\infty)^2$. Define $m(x)=\int_0^\infty y\,p(y\mid x)\,dy$ as an extended nonnegative integral from this same joint law, choosing zero on null marginal fibers. Let $a,b\ge0$, $\delta>0$, and let $(b_k)_{k\ge0}$ be nonnegative, nondecreasing, with $b_0=b$ and $b_k\to\infty$. Suppose $\Pr[X\le a,Y\ge b_k]\le\eta(b_k)$ for every $k\ge0$, where $\eta$ is nonnegative and may take value $+\infty$. Then
--
--   $$\Pr[X\le a,\ m(X)\ge b+\delta]\le\frac1\delta\sum_{k=0}^{\infty}b_{k+1}\eta(b_k).$$
--
--   The series is interpreted in the extended nonnegative reals, preserving infinite conditional means. **Source correction:** the printed sum starts at one despite $b_0=b$; starting at zero includes the missing first interval. Independent moderation remains pending.
-- source:
--   Composable security proof for continuous-variable quantum key distribution with coherent states, arXiv:1408.5689v3, PDF p. 23, Lemma 10, E20–E27

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P61

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P61

attribute [local instance] Classical.propDecidable Classical.decEq

-- The frozen frequency formula specializes exactly to the source alphabet Fin (2 ^ d).

open QAlgorithms.Papers.Independent.Advance50.P30 (empiricalFrequency)

/-- PDF pp.22–23, Lemma 10 (E20–E27), corrected indexing: E22 prints k=1
with b_0=b and omits [b_0,b_1). The sum starts at k=0 as E23's partition requires.
See the source-discrepancy ledger. Integrals and the series are extended. -/
theorem conditionalMean_upper_tail
    (p : ℝ × ℝ → ℝ≥0∞) (hp : Measurable p) [IsProbabilityMeasure (quadrantLaw p)]
    (a b delta : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hdelta : 0 < delta)
    (threshold : ℕ → ℝ) (hthreshold : ∀ k, 0 ≤ threshold k)
    (hmono : Monotone threshold) (hzero : threshold 0 = b)
    (hlim : Tendsto threshold atTop atTop) (eta : ℝ → ℝ≥0∞)
    (htail : ∀ k, quadrantLaw p {v | v.1 ≤ a ∧ threshold k ≤ v.2} ≤ eta (threshold k)) :
    quadrantLaw p {v | v.1 ≤ a ∧ ENNReal.ofReal (b + delta) ≤ densityConditionalMean p v.1} ≤
      (∑' k : ℕ, ENNReal.ofReal (threshold (k + 1)) * eta (threshold k)) /
        ENNReal.ofReal delta := by sorry

end QAlgorithms.Papers.Independent.Intake100.P61

end
